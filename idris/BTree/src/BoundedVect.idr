module BoundedVect
import Data.Vect
import Types
import Lemmas as L

%default total

eitherCong : {f : a -> b} -> Either (x = y) (z = w) -> Either (f x = f y) (f z = f w)
eitherCong {f} (Left Refl) = Left (cong {f} Refl)
eitherCong {f} (Right Refl) = Right (cong {f} Refl)

public
ordInsertVect : Ord a => a -> Vect n a -> (m ** (Vect m a, Either (m = n) (m = S n)))
ordInsertVect {n = Z} x [] = (_ ** ([x], Right Refl))
ordInsertVect {n = (S k)} x (y :: xs) =
  if x == y then
    (_ ** (x :: xs, Left Refl))
  else if x > y then
    let (k ** (xs', result)) = ordInsertVect x xs
    in (S k ** (y :: xs', eitherCong {f=S} result))
  else
    (_ ** (x :: y :: xs, Right Refl))

tryMkBoundedVect : Vect (S n) a ->
                   LTE min n ->
                   LTE n max ->
                   Either (n = max) (BoundedVect (S n) min max a)
tryMkBoundedVect {n} {max} xs minLte lteMax with (decEq n max)
  tryMkBoundedVect  _ _ _ | Yes pf = Left pf
  tryMkBoundedVect {n} {max} xs minLte lteMax | No contra =
    let SnLteMax = L.lemma2 n max lteMax contra
    in Right $ MkBoundedVect xs (lteSuccRight minLte) SnLteMax

public export
ordInsert : Ord a =>
            a ->
            BoundedVect n min max a ->
            Either (Vect (S max) a) (k : Nat ** BoundedVect k min max a)
ordInsert {n} x (MkBoundedVect xs pf1 pf2) with (ordInsertVect x xs)
  ordInsert {n} x (MkBoundedVect xs pf1 pf2) | (n ** (xs', Left Refl)) =
    Right $ (n ** MkBoundedVect xs' pf1 pf2)

  ordInsert {n} x (MkBoundedVect xs pf1 pf2) | (S n ** (xs', Right Refl)) =
    case tryMkBoundedVect xs' pf1 pf2 of
      Left nEqMax => Left $ replace {P=\r => Vect (S r) a} nEqMax xs'
      Right bv => Right (S n ** bv)
