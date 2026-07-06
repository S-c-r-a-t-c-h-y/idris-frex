||| Defines an ordering over the frex carrier
module Frexlet.Monoid.Frex.Order

import Frex

import Frexlet.Monoid.Frex.Structure
import public Data.Order

%hide Control.Relation.Rel

public export
data LtUltList : Rel pen -> Rel ult -> Rel (UltList pen ult) where
  UltimateLT     : {i, j : ult} -> ltUlt i j -> LtUltList ltPen ltUlt (Ultimate i) (Ultimate j)
  UltimateConsLT : LtUltList ltPen ltUlt (Ultimate i) (ConsUlt j y js)
  HeadUltLT      : {i, j : ult} -> ltUlt i j -> LtUltList ltPen ltUlt (ConsUlt i x is) (ConsUlt j y js)
  HeadPenLT      : i = j -> ltPen x y -> LtUltList ltPen ltUlt (ConsUlt i x is) (ConsUlt j y js)
  TailLT         : i = j -> x = y -> LtUltList ltPen ltUlt is js -> 
                   LtUltList ltPen ltUlt (ConsUlt i x is) (ConsUlt j y js)

public export
compareUltList : {ltPen : Rel pen} -> {ltUlt : Rel ult} ->
  (comparePen : (x : pen) -> (y : pen) -> DecOrdering ltPen x y) -> 
  (compareUlt : (x : ult) -> (y : ult) -> DecOrdering ltUlt x y) -> 
  (is, js : UltList pen ult) -> DecOrdering (LtUltList ltPen ltUlt) is js
compareUltList comparePen compareUlt (Ultimate i) (Ultimate j) = case compareUlt i j of
  Lt prf  => Lt $ UltimateLT prf
  Gt prf  => Gt (UltimateLT prf)
  Eq Refl => Eq Refl
compareUltList comparePen compareUlt (Ultimate i) (ConsUlt j y js) = Lt UltimateConsLT
compareUltList comparePen compareUlt (ConsUlt i x is) (Ultimate j) = Gt UltimateConsLT
compareUltList comparePen compareUlt (ConsUlt i x is) (ConsUlt j y js) =
  case compareUlt i j of
    Lt prf  => Lt (HeadUltLT prf)
    Gt prf  => Gt (HeadUltLT prf)
    Eq Refl => case comparePen x y of
      Lt prf  => Lt (HeadPenLT Refl prf)
      Gt prf  => Gt (HeadPenLT Refl prf)
      Eq Refl => case compareUltList comparePen compareUlt is js of
        Lt prf  => Lt (TailLT Refl Refl prf)
        Gt prf  => Gt (TailLT Refl Refl prf)
        Eq Refl => Eq Refl