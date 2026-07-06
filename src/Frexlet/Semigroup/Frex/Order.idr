||| Defines an ordering over the frex carrier
module Frexlet.Semigroup.Frex.Order

import Frex

import Frexlet.Semigroup.Frex.Structure
import Data.List1
import public Data.Order

%default total
%hide Control.Relation.Rel

public export
Uninhabited (MonNE Conc _ Void) where
  uninhabited (OneConc x) = uninhabited x
  uninhabited (ConsConc x _) = uninhabited x

public export
data LtList1Fin : Rel (List1 (Fin n)) where
  HeadLT1 : LtFin x y -> LtList1Fin (x ::: xs) (y ::: ys)
  TailLT1 : x = y -> LtList LtFin xs ys -> LtList1Fin (x ::: xs) (y ::: ys)

public export
compareList1Fin :
  (xs : List1 (Fin n)) -> (ys : List1 (Fin n)) -> DecOrdering LtList1Fin xs ys
compareList1Fin (x ::: xs) (y ::: ys) =
  case compareFin x y of
    Lt prf => Lt (HeadLT1 prf)
    Gt prf => Gt (HeadLT1 prf)
    Eq Refl =>
      case compareList compareFin xs ys of
        Lt prf  => Lt (TailLT1 Refl prf)
        Eq Refl => Eq Refl
        Gt prf  => Gt (TailLT1 Refl prf)

public export
data LtMon : Rel (Mon (Fin n) Void) where
  OneVarsLT : LtList1Fin xs ys -> LtMon (MkVars (OneVars xs)) (MkVars (OneVars ys))

public export
compareMon : (is : Mon (Fin n) Void) -> (js : Mon (Fin n) Void) -> DecOrdering LtMon is js
compareMon (MkVars (OneVars xs)) (MkVars (OneVars ys)) = case compareList1Fin xs ys of
  Lt prf  => Lt (OneVarsLT prf)
  Eq Refl => Eq Refl
  Gt prf  => Gt (OneVarsLT prf)
compareMon (MkVars (OneVars xs)) (MkVars (ConsVars ys is)) = absurd $ uninhabited is
compareMon (MkVars (ConsVars xs is)) (MkVars js) = absurd $ uninhabited is
compareMon (MkVars is) (MkConc js) = absurd $ uninhabited js
compareMon (MkConc is) js = absurd $ uninhabited is

