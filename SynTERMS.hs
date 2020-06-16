module SynTerms where


import System.IO ( stdin, hGetContents )
import System.Environment ( getArgs, getProgName )
import System.Exit ( exitFailure, exitSuccess )

import Data.Char
import Data.List

import LexTERMS
import ParTERMS
import SkelTERMS
import PrintTERMS
import AbsTERMS




import ErrM

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = if v > 1 then putStrLn s else return ()

runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s = let ts = myLLexer s in case p ts of
           Bad s    -> do putStrLn "\nParse              Failed...\n"
                          putStrV v "Tokens:"
                          putStrV v $ show ts
                          putStrLn s
                          exitFailure
           Ok  tree -> do putStrLn "\nParse Successful!"
                          showTree v tree

                          exitSuccess

showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

unErr :: (Err Term) -> Term
unErr (Ok a) = a
unErr (Bad errMsg) = error ("Parsing Errors" ++ errMsg)


------------------------------------------------------------------------
-- "Syntactic" analyse on [ logical ] Terms                                  --
------------------------------------------------------------------------

data STerm = STClause Ident [STerm] | STVar Ident | STAtom Ident
  deriving (Eq, Ord, Show, Read)

sTerm :: Term -> STerm
sTerm t =
  case t of
    TClause i l -> STClause i (map sTerm l)
    TIdent (Ident i) ->
      if isUpper (head i) then (STVar (Ident i)) else (STAtom (Ident i))

spTerm :: String -> STerm
spTerm s = sTerm $ unErr $ pTerm $ myLLexer s

data Variable = Var Ident
  deriving (Eq, Ord, Show, Read)

showVar :: Variable -> String
showVar v = v2s v

showSTerm :: STerm -> String
showSTerm st =
 case st of
  STAtom (Ident i) -> i
  STVar (Ident i) -> i
  STClause (Ident c) l ->
    c ++
    " ( " ++
    (if length l > 0
      then 
        (showSTerm(head l) ++
        (foldl (++) "" (map (\x -> ", " ++ (showSTerm(x) )) (tail l))))
      else "") ++
    " )"
  -- sth -> show sth

putSTerm :: STerm -> IO ()
putSTerm x = putStr (showSTerm x)

showSubst1 :: (Variable, STerm) -> String
showSubst1 (v, st) = (showVar v) ++ " -> " ++ (showSTerm st) ++ "\n"

-- showSubstitution:
showSubst :: [(Variable, STerm)] -> String
showSubst l =
  if length l > 0 then foldl (++) "" $ map (\(x,y) -> showSubst1 (x,y)) l
  else "Empty substitution.\n"

putSubst :: [(Variable, STerm)] -> IO ()
putSubst x = putStr (showSubst x)

------------------------------------------------------------------------
-- tests 1.1 .. 1.2                                                   --
------------------------------------------------------------------------

t1 = "label(gh(V2, ba), V1)"
t2 = "label(V1, cd(ef, V2))"
t3 = "l(A,m(B,n(C,D,E,o(F,G,p(S),T),U,W),Y),Z,A,r(),s(),t(u),w(y,z))"

pt1 = unErr $ pTerm $ myLLexer t1
pt2 = unErr $ pTerm $ myLLexer t2
pt3 = unErr $ pTerm $ myLLexer t3

st1 = sTerm pt1
st2 = sTerm pt2
st3 = sTerm pt3

------------------------------------------------------------------------
------------------------------------------------------------------------


unify1 :: (STerm, STerm) -> [(Variable, STerm)]
unify1 (st1, st2) = unify st1 st2

-- [ (head (findVariables st1), st2) ]
unify :: STerm -> STerm -> [(Variable, STerm)]
unify st1 st2 =
  case (st1, st2) of
    (STClause (Ident id1) l1, STClause (Ident id2) l2) ->
      if id1 /= id2 then
        error $ "Clause names '" ++ id1 ++"' and '" ++ id2 ++"' differ."
      else
        if length l1 /= length l2 then
          error "Different arity of clauses."
        else
          foldl (++) [] $ map unify1 (zip l1 l2)
    (STVar iia@(Ident ia), STVar iib@(Ident ib)) ->
      if ia == ib
        then [(Var (Ident ("$$" ++ ia)), STAtom (Ident "?free variable"))]
        else [(Var (Ident ("$$" ++ ia)), STAtom (Ident (ia ++ " == " ++ ib))),
              (Var (Ident ("$$" ++ ib)), STAtom (Ident (ib ++ " == " ++ ia)))]
      
    (STVar ii1@(Ident i1), st3) -> 
      if (find (\x -> x == (Var ii1)) (findVariables st3)) /= Nothing
        then error $ "Variable '" ++ i1 ++ "' recurrs in required substitution."
        else [(Var ii1, st3)]
    (st4, STVar ii2@(Ident i2)) ->
      if (find (\x -> x == (Var ii2)) (findVariables st4)) /= Nothing
        then error $ "Variable '" ++ i2 ++ "' recurrs in required substitution."
        else [(Var ii2, st4)]
    (STAtom (Ident a1), STAtom (Ident a2)) ->
      if a1 /= a2 then error $ "Atoms '" ++ a1 ++ "' and '" ++ a2 ++ "' differ."
      else []
    (st5, st6) -> 
      error $ "Unreachable? Terms '" ++ show(st5) ++ 
                           "' and '" ++ show(st6) ++ "can not be unified."

findVariables :: STerm -> [Variable]
findVariables st =
  case st of
    STClause _ l -> foldl (++) [] $ map findVariables l
    STVar i      -> [Var i]
    STAtom _     -> []

v2s :: Variable -> String
v2s (Var (Ident s)) = s

vs1 = findVariables st1
vs2 = findVariables st2
vs3 = findVariables st3

-- nastepny krok - zainstalowac sobie haskell-mode
-- przemianowywanie zmiennych - dopiero w SLD - rezolucji

-- unify (spTerm t5) (spTerm t4)

------------------------------------------------------------------------
------------------------------------------------------------------------

replaceWith :: [String] -> (String, String) -> [String]
replaceWith [] (s1, s2) = []
replaceWith (h:s) (s1, s2) = 
  if h == s1 then (s2:(replaceWith s (s1, s2))) else ( h:(replaceWith s (s1, s2)))

-- foldl replaceWith ["a","e","c", "a", "c"] [("a","hi"),("c","jk"),("e","lm")]

------------------------------------------------------------------------
------------------------------------------------------------------------

applySubst :: STerm -> (Variable, STerm) -> STerm
applySubst st2 subst@((Var (Ident i)), st1) = 
  case st2 of
    STVar (Ident i1) -> if i1 == i then st1 else STVar (Ident i1)
    STClause (Ident i2) l1 -> 
      STClause (Ident i2) (map (\st3 -> applySubst st3 subst) l1)
    STAtom (Ident i3) -> STAtom (Ident i3)

applySubsts :: [(Variable, STerm)] -> STerm -> STerm
applySubsts ss st = foldl applySubst st ss

-- w jakiej postaci term do podstawienia na zmienna?
{- -}
merge2Substs :: Variable -> STerm -> STerm -> [(Variable, STerm)]
merge2Substs v1@(Var (Ident i)) st1 st2 = 
  let succSubst = (unify st1 st2) in 
    (succSubst ++ [(v1, applySubsts succSubst st1)])
{- -}
-- i czy to naiwne, a nawet jesli to czy jednak w pelni dzialajace?
--
-- TODO: 
--   1.) -> find Repetitions In Substituting Variables
--   2.) -> consequently, for each variable that repeats:
--          2.1) merge 2 or more such repetitions by folding: /foldl, possibly/
--               merge [a1/v .. an/v] -> 
--                 merge(a1, merge a2(...merge(an-2,merge(an-1, an)...)

------------------------------------------------------------------------
-- tests 2.1 , 3.1                                                    --
------------------------------------------------------------------------

t4 = "l1(V,  m1(m2), W,   X,   m3(m4), m5(Y),   m6(m7,m8), m11(m12,m13), m14())"
t5 = "l1(m9, Z     , m10, m11, A,      m5(m10), m6(m7,B),  C,            D)"
t6 = "l1(V,  Z     , W,   m11, A,      m5(Y),   m6(m7,B),  m11(m12,m13), m14())"
ta = "l1(V,  m1(m2), W,   X,   m3(m4), m5(Y),   m6(m7,m8), m11(m12,m13), D)"

t7 = "l2(a, b, K, L, a)"
t8 = "l2(K, L, a, b, K)"

------------------------------------------------------------------------
------------------------------------------------------------------------

-- putStr $ showSubst $ unify (spTerm t5) (spTerm t4)

-- showSTerm $ applySubsts (unify (spTerm t5) (spTerm t4)) (spTerm t4)
-- showSTerm $ applySubsts (unify (spTerm t5) (spTerm t4)) (spTerm t5)

sp4out = applySubsts (unify (spTerm t5) (spTerm t4)) (spTerm t4)
sp5out = applySubsts (unify (spTerm t5) (spTerm t4)) (spTerm t5)

-- assert sp4out == sp5out

spt9  = STClause (Ident "step1Test") [(spTerm t4), (spTerm t7), (spTerm t5), (spTerm t8), (spTerm ta)]
t10   = "step1Test(I, J, I, J, I)"
spt10 = spTerm t10

substAt :: Variable -> [(Variable, STerm)] -> (Variable, STerm)
substAt v vstl = head $ filter (\(a,b) -> a == v) vstl 
substNotAt :: Variable -> [(Variable, STerm)] -> [(Variable, STerm)]
substNotAt v vstl = filter (\(a,b) -> a /= v) vstl 
varSTermPair2STerm :: (Variable, STerm) -> STerm
varSTermPair2STerm (a, b) = b

-- unify (spTerm "I") (spTerm "I")
-- *** Exception: Variable 'I' recurrs in required substitution.
-- CallStack (from HasCallStack):
--  error, called at SynTERMS.hs:104:14 in main:SynTerms
-- *SynTerms> 

-- open the file lab/potter.pl and think about prolog example giving free variable / used twice in it /
-- maybe later / coding sld resulution stage / make such example

-- Użyć tych dwóch termów i jeszcze trzech, tak, aby było do scalenia: J, J, I, I, I :
-- putStr $ showSubst $ unify spt9 spt10

--   poprzez:
--
-- 1) find variables with two or more occurences in substitution
-- 2) foldl construction of s1 and s2 .. up to si
--    ... by taking left argument term to merge from step i-1 of foldl,
--         ... and right argument term to merge from substitution i,
--         ... and effectively unifying all the terms hopefully substituted
--             on a given
--             Variable.

-- putSubst $ merge2Substs (Var (Ident "I")) (spTerm t4) (spTerm t5)
termToSubst :: Variable -> [(Variable, STerm)] -> STerm
termToSubst vi@(Var (Ident i)) substs = varSTermPair2STerm (substAt vi substs)

s1 = merge2Substs (Var (Ident "I")) (spTerm t4) (spTerm t5)
s2 = merge2Substs (Var (Ident "I")) (varSTermPair2STerm (substAt (Var (Ident "I")) s1)) (spTerm t6)

------------------------------------------------------------------------
-- focusOnSubstOfVar :: Variable -> [(Variable, STerm)] -> (Variable, STerm)
-- focusOnSubstOfVar = SubstOfVar
------------------------------------------------------------------------
------------------------------------------------------------------------
-- test 4.1                                                           --
------------------------------------------------------------------------

varJ = (Var (Ident "J"))

tb = "l2(a, b, O, L, a)"
th = "l3(c, d, M, N, d)"
tc = "l2(O, L, a, b, K)"
ti = "l3(N, M, d, c, d)"
td = "l2(K, L, a, L, a)"
te = "l2(a, b, a, b, K)"

tf = "l3(J,I,J,I,J,J,J)"
tg = "l3(" ++ tb ++ ", " ++ th ++ ", " ++ tc ++ ", " ++ ti ++ ", " ++ td ++ ", " ++ te ++ ")"

s3 = merge2Substs varJ           (spTerm tb) (spTerm tc)
s4 = merge2Substs varJ (termToSubst varJ s3) (spTerm td)
s5 = merge2Substs varJ (termToSubst varJ s4) (spTerm te)

unifyS :: String -> String -> [(Variable, STerm)]
unifyS t1 t2 = unify (spTerm t1) (spTerm t2)

-- (+) TODO: blad: unify clause/5 clause/4 odnosi sukces / przyklad linijke nizej /
-- (+) TODO: unifyS tf tg     daje J -> a) , J -> b) , J -> c) , J -> d)
--       a powinno zawierac tego foldowanego merge, jak w przykladzie
--       s3 = .. , s4=.. , s5 = ..
-- (-) (1)  - uwaga na gubienie pozostałych podstawień
------------------------------------------------------------------------
------------------------------------------------------------------------
-- groupBy (==) $ sort [4,3,4,3,4,3,5,6,5,6,5,6]
-- [[3,3,3],[4,4,4],[5,5,5],[6,6,6]]

frontOfTupleSame :: Eq(a) => (a,b) -> (a,b) -> Bool
frontOfTupleSame (a1, b1) (a2, b2) = (a1 == a2)

pairToFirst :: (a,b) -> a
pairToFirst (a1,b1) = a1

pairToSecond :: (a,b) -> b
pairToSecond (a1,b1) = b1

pairsToSecond :: [(a,b)] -> [b]
pairsToSecond l = map pairToSecond l

-- rectifies from given Substitutions Term designated to substitute On given Variable 
-- focus On Term Substituted On Variable
focusOnTermSubstOnVar :: Variable -> [(Variable, STerm)] -> STerm
focusOnTermSubstOnVar = termToSubst

mergeNSubsts :: [(Variable, STerm)] -> (Variable, STerm)
mergeNSubsts ss =
  let sts = pairsToSecond ss in
    (let v = pairToFirst (head ss) in
      (v, (foldl1 (merge2SubstsForFolding v) sts))
    )

-- foldl1 (\x -> (focusOnTermSubstOnVar v (merge2Substs v a1 a2)) sts
-- caveat: we loose / like in notice above / substitutions on rest of variables
merge2SubstsForFolding :: Variable -> STerm -> STerm -> STerm
merge2SubstsForFolding v st1 st2 =
  focusOnTermSubstOnVar v (merge2Substs v st1 st2)

-- sts: [STerm]
-- v: Variable      

mergeSubsts1 :: [(Variable, STerm)] -> [[(Variable, STerm)]]
mergeSubsts1 sts = groupBy (frontOfTupleSame) (sort sts)

showSubstAndSepare :: [(Variable, STerm)] -> String
showSubstAndSepare sts = showSubst sts ++ "-----------------\n"

putGroups :: [[(Variable, STerm)]] -> IO ()
putGroups gsts = putStr $ foldl1 (++) $ map showSubstAndSepare gsts

-- zalozenie : length sts > 0
mergeSubsts :: [(Variable, STerm)] -> [(Variable, STerm)]
mergeSubsts sts =
  if length sts > 0 then
    map mergeNSubsts (groupBy (frontOfTupleSame) (sort sts))
  else
    []

------------------------------------------------------------------------
-- test 5.1, 5.2                                                      --
------------------------------------------------------------------------
--
-- TODO: (-) (1)
-- caveat solution:
--
--   replace use of: foldl1 :: (STerm -> STerm -> STerm) -> [STerm] -> STerm
--             with: foldl1 :: (Subst -> Subst -> Subst) -> [Subst] -> Subst
--             where: Subst is [(Variable, STerm)]
--
-- challenge: Should one keep repeated variable substitutions separately (1a)
--            / and how / from the rest of variables? And what, if there also arises repetition ? (1b)
--
-- maybe with acumulator:
--
-- foldl1 :: (Subst -> Subst -> Subst) -> [Subst] -> Subst
-- where: Subst is ([(Variable, STerm)], [(Variable, STerm)])
--   and first element of this pair is assured to be set for a single variable,
-- or even: is ([STerm], [(Variable, STerm)]), where second element does not substitute on 'v' (1a)

-- TODO: (-) (1) spróbować pokazać / lub pokazać, że przeciwnie / że wolne zmienne zostaną nie wyświetlone

-- putSubst $ unify spt9 spt10
-- putGroups $ mergeSubsts1 $ unify spt9 spt10
-- putSubst $ mergeSubsts $ unify spt9 spt10

-- putSubst $ unify spt9 spt10
-- putGroups $ mergeSubsts1 $ unifyS tf tg
-- putSubst $ mergeSubsts $ unifyS tf tg
--

{-
mergeNSubsts :: [(Variable, STerm)] -> (Variable, STerm)
 mergeNSubsts ss =
  let sts = pairsToSecond ss in
    (let v = pairToFirst (head ss) in
      (v, (foldl1 (merge2SubstsForFolding v) sts))
    )

merge2SubstsForFolding :: Variable -> STerm -> STerm -> STerm
merge2SubstsForFolding v st1 st2 =
  focusOnTermSubstOnVar v (merge2Substs v st1 st2)
-}
-- foldl1 (\x -> (focusOnTermSubstOnVar v (merge2Substs v a1 a2)) sts
-- caveat: we loose / like in notice above / substitutions on rest of variables

-- ///// Zapewne można zrobić fold po [STerm] z samym akumulatorem, próbuję zrobić to zbyt szeroko

-- Ta funkcja bieze liste podstawien Var1 <- Term1 .. VarN <- TermN
-- i próbuje laczyc z pomoca unifikacji gdy zmienna na tej liscie sie powtarza 
-- zalozenie: lista podstawien zawiera choc jeden element
mergeNSubstsAcc :: [(Variable, STerm)] -> (Variable, (STerm, [(Variable, STerm)]))
mergeNSubstsAcc ss =
  let v = pairToFirst (head ss) in
    (let sts = pairsToSecondWithBlankAcc ss in
      (v, (foldl1 (merge2SubstsForFoldingAcc v) sts))
    )

thisToSubst :: (Variable, (STerm, [(Variable, STerm)])) -> [(Variable, STerm)]
thisToSubst (v, (st, sts)) = [(v,st)] ++ sts

pairToSecondWithBlankAcc :: (a,b) -> (b,[c])
pairToSecondWithBlankAcc (a1,b1) = (b1,[])
pairsToSecondWithBlankAcc :: [(a,b)] -> [(b,[c])]
pairsToSecondWithBlankAcc l = map pairToSecondWithBlankAcc l


-- Ta funkcja bierze zmienną.
-- Potem dwa termy, unifikuje je.
-- Po czym otrzymane podstawienie aplikuje do pierwszego termu.
-- 
-- Na końcu zwraca to otrzymane podstawienie,
--   rozszerzone o podstawienie otrzymanego w ostatnim kroku termu na zmienną, będącą pierwszym argumentem.
-- 
-- merge2Substs :: Variable -> STerm -> STerm -> [(Variable, STerm)]

-- ///// Zapewne można zrobić fold po [STerm] z samym akumulatorem, próbuję zrobić to zbyt szeroko
-- sygnatura zatem:
{-
merge2SubstsForFoldingAcc :: Variable -> (STerm,[(Variable,STerm)]) -> STerm -> (STerm,[(Variable,STerm)])
merge2SubstsForFoldingAcc v (st1, acc1) (st2, _) =
  let (st3, acc3) = focusOnTermSubstOnVarAndAccumulateRest v (merge2Substs v st1 st2) in
    (st3, acc3 ++ acc1)
-}

merge2SubstsForFoldingAcc ::
  Variable -> (STerm,[(Variable,STerm)]) -> (STerm,[(Variable,STerm)]) -> (STerm,[(Variable,STerm)])
merge2SubstsForFoldingAcc v (st1, acc1) (st2, _) =
  let (st3, acc3) = focusOnTermSubstOnVarAndAccumulateRest v (merge2Substs v st1 st2) in
    (st3, acc3 ++ acc1)

-- ///// Zapewne można zrobić fold po [STerm] z samym akumulatorem, próbuję zrobić to zbyt szeroko
focusOnTermSubstOnVarAndAccumulateRest :: Variable -> [(Variable,STerm)] -> (STerm, [(Variable, STerm)])
focusOnTermSubstOnVarAndAccumulateRest vi@(Var (Ident i)) substs =
  ( (varSTermPair2STerm (substAt vi substs)), (substNotAt vi substs) )

------------------------------------------------------------------------
-- intermission: KolaBolaLabKabOla                                    --
------------------------------------------------------------------------

sth = map mergeNSubstsAcc $ mergeSubsts1 $ unifyS tf tg
sth1 = map thisToSubst sth
-- putGroups sth1

-- putSubst $ foldl1 (++) $ map thisToSubst $ map mergeNSubstsAcc $ mergeSubsts1 $ foldl1 (++) sth1
--            \----------------------------------\/----------------------------/
--                              ... and loop this until no progress
--
--                                             the end


mergingUnifyingStep :: [(Variable,STerm)] -> [(Variable,STerm)]
mergingUnifyingStep sts = foldl1 (++) $ map thisToSubst $ map mergeNSubstsAcc $ mergeSubsts1 sts

mergingUnifyingLoop :: [(Variable,STerm)] -> [(Variable,STerm)]
mergingUnifyingLoop sts =
 let sts1 = mergingUnifyingStep sts in if sts1 == sts then sts else mergingUnifyingLoop sts1

unifyMergeS :: String -> String -> [(Variable,STerm)]
unifyMergeS t1 t2 =
  let sts1 = unifyS t1 t2 in
  if length sts1 > 0 then mergingUnifyingLoop sts1 else sts1

unifyMerge :: STerm -> STerm -> [(Variable,STerm)]
unifyMerge st1 st2 =
  let sts1 = unify st1 st2 in
  if length sts1 > 0 then mergingUnifyingLoop sts1 else sts1

-- do sprawdzenia:
--
-- TODO: 1b),
-- TODO: oraz: ?free variable
-- TODO: oraz: V1 == V2
--
-- Zrobione. Dodałem "$$" przed nazwami zmiennych ... (Powtórzenia? tak jest fajniej.)
--
-- TODO: unifikuje / bez ostrzeżenia / clause/4 i clause/5