module Data.Order

import public Data.Relation

import Data.Nat
import Data.Fin
import Data.Vect

import Data.Setoid

%hide Control.Relation.Rel

------------------------ DEFINITIONS ------------------------

public export
record IsOrder (relation : Relation.Rel t) where
  irreflexive : (x       : t) -> Not (relation x x)
  asymmetric  : (x, y    : t) -> relation x y -> Not (relation y x)
  transitive  : (x, y, z : t) -> relation x y -> relation y z 
                              -> relation x z

public export
data DecOrdering : (lt : Rel a) -> a -> a -> Type where
  Lt : {x, y : a} -> {lt : Rel a} -> lt x y  -> DecOrdering lt x y
  Eq : {x, y : a} -> {lt : Rel a} -> x = y   -> DecOrdering lt x y
  Gt : {x, y : a} -> {lt : Rel a} -> lt y x  -> DecOrdering lt x y

-- a set equiped with a decidable strict order
public export
record StrictOrd (U : Type) where
  constructor MkStrictOrd
  lt : Rel U
  ltDec : DecRel lt
  ltIsOrder : IsOrder lt
  compare : (x : U) -> (y : U) -> DecOrdering lt x y

public export
record OrdSetoid where
  constructor MkOrdSetoid
  setoid : Setoid
  decOrd : StrictOrd (U setoid)

public export
Cast OrdSetoid Setoid where
  cast decSet = decSet.setoid

public export 0
U : OrdSetoid -> Type
U x_set = U x_set.setoid

------------------------ IMPLEMENTATIONS ------------------------

public export
data LexicographicLT : (lt1 : Rel a) -> (lt2 : Rel b) -> Rel (a, b) where
  FstLT : {x1, x2 : a} -> {y1, y2 : b} -> lt1 x1 x2 -> LexicographicLT lt1 lt2 (x1, y1) (x2, y2)
  SndLT : {x1, x2 : a} -> {y1, y2 : b} -> x1 = x2 -> lt2 y1 y2 -> LexicographicLT lt1 lt2 (x1, y1) (x2, y2)

public export
compareLexicographic : {lt1 : Rel a} -> {lt2 : Rel b} -> 
  (cmp1 : (x, y : a) -> DecOrdering lt1 x y) ->
  (cmp2 : (x, y : b) -> DecOrdering lt2 x y) ->
  (x, y : (a, b)) -> DecOrdering (LexicographicLT lt1 lt2) x y
compareLexicographic cmp1 cmp2 (x1, y1) (x2, y2) = 
  case cmp1 x1 x2 of
    Lt prf  => Lt (FstLT prf)
    Gt prf  => Gt (FstLT prf)
    Eq Refl => case cmp2 y1 y2 of
      Lt prf  => Lt (SndLT Refl prf)
      Gt prf  => Gt (SndLT Refl prf)
      Eq Refl => Eq Refl

public export
compareNat : (n, m : Nat) -> DecOrdering LT n m
compareNat 0 0 = Eq Refl
compareNat 0 (S j) = Lt ltZero
compareNat (S k) 0 = Gt ltZero
compareNat (S k) (S j) = case compareNat k j of
  Lt prf  => Lt (LTESucc prf)
  Gt prf  => Gt (LTESucc prf)
  Eq Refl => Eq Refl

public export
data LtUnit : Rel Unit where -- Unit has a single constructor, so no element is strictly smaller than another

public export
compareUnit : (x : Unit) -> (y : Unit) -> DecOrdering LtUnit x y
compareUnit () () = Eq Refl

public export
data LtBool : Rel Bool where
  FalseTrueLT : LtBool False True

public export
compareBool : (b1, b2 : Bool) -> DecOrdering LtBool b1 b2
compareBool False False = Eq Refl
compareBool False True = Lt FalseTrueLT
compareBool True False = Gt FalseTrueLT
compareBool True True = Eq Refl

public export
data LtFin : Rel (Fin n) where
  FZLT : LtFin FZ (FS y)
  FSLT : LtFin x y -> LtFin (FS x) (FS y)

public export
compareFin : (x : Fin n) -> (y : Fin n) -> DecOrdering LtFin x y
compareFin FZ FZ = Eq Refl
compareFin FZ (FS y) = Lt FZLT
compareFin (FS x) FZ = Gt FZLT
compareFin (FS x) (FS y) =
  case compareFin x y of
    Lt prf  => Lt (FSLT prf)
    Eq Refl => Eq Refl
    Gt prf  => Gt (FSLT prf)

public export
data LtList : Rel a -> Rel (List a) where
  NilLT  : {lt : Rel a} -> LtList lt [] (y :: ys)
  HeadLT : {lt : Rel a} -> lt x y -> LtList lt (x :: xs) (y :: ys)
  TailLT : {lt : Rel a} -> x = y -> LtList lt xs ys -> LtList lt (x :: xs) (y :: ys)

public export
compareList :
  {lt : Rel a} ->
  (cmp : (x : a) -> (y : a) -> DecOrdering lt x y) ->
  (xs : List a) -> (ys : List a) -> 
  DecOrdering (LtList lt) xs ys
compareList _ [] [] = Eq Refl
compareList _ [] (y :: ys) = Lt NilLT
compareList _ (x :: xs) [] = Gt NilLT
compareList cmp (x :: xs) (y :: ys) =
  case cmp x y of
    Lt prf  => Lt (HeadLT prf)
    Gt prf  => Gt (HeadLT prf)
    Eq Refl =>
      case compareList cmp xs ys of
        Lt prf  => Lt (TailLT Refl prf)
        Eq Refl => Eq Refl
        Gt prf  => Gt (TailLT Refl prf)

public export
data LtVect : Rel a -> Rel (Vect n a) where
  VHeadLT : {lt : Rel a} -> lt x y -> LtVect lt (x :: xs) (y :: ys)
  VTailLT : {lt : Rel a} -> x = y -> LtVect lt xs ys -> LtVect lt (x :: xs) (y :: ys)

public export
compareVect :
  {lt : Rel a} ->
  (cmp : (x : a) -> (y : a) -> DecOrdering lt x y) ->
  (xs : Vect n a) -> (ys : Vect n a) -> 
  DecOrdering (LtVect lt) xs ys
compareVect _ [] [] = Eq Refl
compareVect cmp (x :: xs) (y :: ys) =
  case cmp x y of
    Lt prf  => Lt (VHeadLT prf)
    Gt prf  => Gt (VHeadLT prf)
    Eq Refl =>
      case compareVect cmp xs ys of
        Lt prf  => Lt (VTailLT Refl prf)
        Eq Refl => Eq Refl
        Gt prf  => Gt (VTailLT Refl prf)

