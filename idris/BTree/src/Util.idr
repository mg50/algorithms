module Util
import Data.Vect

%access public export
%default total

data InterleavedList : Type -> Type -> Type where
  More : a -> b -> Lazy (InterleavedList a b) -> InterleavedList a b
  NoMore : b -> InterleavedList a b

interleave : Vect n a -> Vect (S n) b -> InterleavedList a b
interleave [] [y] = NoMore y
interleave (x :: xs) (y :: ys) = More x y (interleave xs ys)

-- make this tail-recursive
vsplit : Vect (n + m) a -> (Vect n a, Vect m a)
vsplit {n = Z} v = ([], v)
vsplit {n = (S k)} (x :: xs) =
  let (left, right) = vsplit xs
  in (x::left, right)

vsplitOrd : Ord a => a -> Vect k a -> (n : Nat ** m : Nat ** (Vect n a, Vect m a, n + m = k))
vsplitOrd {k = Z} x [] = (0 ** 0 ** ([], [], Refl))
vsplitOrd {k = (S j)} x (y :: xs) =
  if x <= y then
    (0 ** S j ** ([], y :: xs, Refl))
  else
    let (n ** m ** (left, right, pf)) = vsplitOrd x xs
    in (S n ** m ** (y :: left, right, cong pf))

lemma : (n : Nat) -> S (2*n) = n + S n
lemma n =
  let a = the (2*n = n + n) $ rewrite (plusZeroRightNeutral n)
                              in Refl
      b = cong {f=S} a
      c = plusSuccRightSucc n n
  in trans b c

retypeVect : n = m -> Vect n a -> Vect m a
retypeVect {n} = replace {P=\k => Vect k a}

trisect : Vect (S (2*n)) a -> (Vect n a, a, Vect n a)
trisect {n} xs =
  let (left, x::right) = vsplit (retypeVect (lemma n) xs)
  in (left, x, right)

-- make this tail-recursive
findInsertionLoc : Ord a =>
                   a ->
                   Vect n a ->
                   Either (Vect n a)
                          (k : Nat ** LTE k n)
findInsertionLoc {n = Z} x [] = Right (Z ** LTEZero)
findInsertionLoc {n = (S k)} x (y :: xs) =
  if x == y then
    Left (x::xs)
  else if x < y then
    Right (k ** lteSucc k)
  else
    case findInsertionLoc x xs of
      Left xs' => Left (y :: xs')
      Right (k ** pf) => Right (S k ** LTESucc pf)
  where
    lteSucc : (n : Nat) -> LTE n (S n)
    lteSucc Z = LTEZero
    lteSucc (S k) = LTESucc (lteSucc k)

vectInsert : (idx : Nat) -> a -> Vect n a -> Vect (S n) a
vectInsert _ x [] = [x]
vectInsert Z x xs = x :: xs
vectInsert (S k) x (y :: xs) = y :: vectInsert k x xs

vectInsertOrd : Ord a => a -> Vect n a -> Vect (S n) a
vectInsertOrd x [] = [x]
vectInsertOrd x (y::xs) = if x < y then
                             x::y::xs
                          else
                            y :: vectInsertOrd x xs
-- vectInsert Z x xs = x :: xs
-- vectInsert (S k) x (y :: xs) = y :: vectInsert k x xs

lteAdditionLemma : {n, m : Nat} -> LTE n m -> (k : Nat ** S m = n + S k)
lteAdditionLemma {n=Z} {m} lte = (m ** Refl)
lteAdditionLemma {n=(S n)} {m=(S m)} (LTESucc lte) =
  let (k ** eq) = lteAdditionLemma {n} {m} lte
  in (k ** cong eq)
