# UnificationInHaskell

Aby zbudować TestTERMS, wykonać:

  ./mk
  make
  
Przetestować:

  echo "g(h(i(j)))" | ./TestTERMS

Eksperymenty z unifikacją:

  ghci SynTERMS.hs
    
  *SynTERMS> *SynTerms> showSTerm spt10
"step1Test ( I, J, I, J, I )"
  *SynTerms> showSTerm spt9
"step1Test ( l1 ( V, m1 ( m2 ), W, X, m3 ( m4 ), m5 ( Y ), m6 ( m7, m8 ), m11 ( m12, m13 ), m14 (  ) ), l2 ( a, b, K, L, a ), l1 ( m9, Z, m10, m11, A, m5 ( m10 ), m6 ( m7, B ), C, D ), l2 ( K, L, a, b, K ), l1 ( V, m1 ( m2 ), W, X, m3 ( m4 ), m5 ( Y ), m6 ( m7, m8 ), m11 ( m12, m13 ), D ) )"
  *SynTerms> putStr $ showSubst $ unifyMerge spt10 spt9
  ...
