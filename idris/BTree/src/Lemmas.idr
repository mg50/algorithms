module Lemmas

%access public export
%default total

lemma1 : S k = n + S m -> n + S (S m) = S (S k)
lemma1 {n} {m} pf = rewrite pf in
                    rewrite plusSuccRightSucc n (S m) in
                    Refl

lemma2 : (n, max : Nat) -> LTE n max -> Not (n = max) -> LT n max
lemma2 Z Z _ nNotEqMax = absurd (nNotEqMax Refl)
lemma2 Z (S max) _ _ = LTESucc LTEZero
lemma2 (S n) (S max) (LTESucc nLteMax) SnNotEqSmax =
  LTESucc (lemma2 n max nLteMax nNotEqMax)
  where
    nNotEqMax : Not (n = max)
    nNotEqMax nEqMax = SnNotEqSmax (cong nEqMax)

lemma3 : Not (n = m) -> Not (S n = m + 1)
lemma3 {n} {m} contra = \pf => let eq = sym (plusSuccRightSucc m 0)
                                   pf' = replace {P = \r => S n = r} eq pf
                                   pf'' = replace {P = \r => S n = S r} (plusZeroRightNeutral m) pf'
                               in contra (succInjective n m pf'')

lemma4 : (n : Nat) -> S (S (2*n)) = (S n) + (S n)
lemma4 Z = Refl
lemma4 (S k) = rewrite plusZeroRightNeutral k in
               rewrite plusSuccRightSucc k (S k) in
               Refl

lemma5 : (n : Nat) -> LTE (S n) (2*n + 1)
lemma5 n = let x = the (LTE n (2*n)) (lteAddRight n)
               y = LTESucc x
           in replace {P = \r => LTE (S n) r} (sublemma n) y
  where
    sublemma : (n : Nat) -> S (n + (n + 0)) = 2*n + 1
    sublemma n = rewrite plusZeroRightNeutral n in
                 rewrite sym $ plusZeroRightNeutral (n + n) in
                 rewrite plusSuccRightSucc (n+n) 0 in
                 rewrite plusZeroRightNeutral (n+n) in
                 Refl

lemma6 : (n : Nat) -> LTE 1 n -> LTE 1 (2*n)
lemma6 n pf = rewrite plusZeroRightNeutral n in
              lteTransitive pf (lteAddRight n)

lemma7 : (n : Nat) -> LTE 1 n -> LTE 2 ((2*n) + 1)
lemma7 n pf = let result = LTESucc (lemma6 n pf)
              in rewrite plusCommutative (n + (n + 0)) 1 in
              result
