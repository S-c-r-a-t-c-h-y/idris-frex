||| This was the first attempt at implementing the free commutative semigroup
||| over the set of n variables.

module Frexlet.Semigroup.Commutative.Free

import Frex

import Frexlet.Semigroup.Commutative.Theory
import Frexlet.Semigroup.Commutative.Dirac
import Frexlet.Semigroup.Commutative.Notation.Core

import Data.Vect
import Data.Vect.Quantifiers
import Data.Maybe

import Data.List1

import Data.Setoid

import Decidable.Equality
import Decidable.Decidable

%default total

public export
interface DecOrd (rel : Relation.Rel t) where
  decOrd : (x1 : t) -> (x2 : t) -> Dec (rel x1 x2)

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
  eq : DecEq U
  lt : Rel U
  ltDec : DecOrd lt
  ltIsOrder : IsOrder lt
  compare : (x : U) -> (y : U) -> DecOrdering lt x y


public export
record DecSet where
  constructor MkDecSet
  0 U : Type
  decOrd : StrictOrd U

public export
data Sorted : (lt : Rel a) -> List1 (a, Nat) -> Type where
  SortedSingle : {lt : Rel a} -> {x : a} -> {nx : Nat} -> Sorted lt ((x, nx) ::: [])
  SortedCons   : {lt : Rel a} -> {x, y : a} -> {nx, ny : Nat} -> {ys : List (a, Nat)} -> 
                 lt x y -> Sorted lt ((y, ny) ::: ys) -> Sorted lt ((x, nx) ::: (y, ny) :: ys)
  
-- public export
-- sortedTail : Sorted ((x, nx) ::: (y, ny) :: ys) -> Sorted ((y, ny) ::: ys)
-- sortedTail (SortedCons x y) = y

public export
record FreeCarrier (x : DecSet) where
  constructor MkFreeCarrier
  coeffs : List1 (U x, Nat)
  sorted : Sorted x.decOrd.lt coeffs

public export
eqHead : {x_set : DecSet} -> (x, y : U x_set) -> (nx, ny : Nat) ->
  (xs, ys : List (U x_set, Nat)) ->
  (prf1 : Sorted x_set.decOrd.lt ((x, nx) ::: xs)) ->
  (prf2 : Sorted x_set.decOrd.lt ((y, ny) ::: ys)) ->
  (prf : MkFreeCarrier {x = x_set} ((x, nx) ::: xs) prf1 = MkFreeCarrier {x = x_set} ((y, ny) ::: ys) prf2) ->
  x = y
eqHead x x nx nx xs xs prf1 prf1 Refl = Refl
  
public export
FreeSetoid : (x : DecSet) -> Setoid
FreeSetoid x = MkSetoid
  { U = FreeCarrier x
  , equivalence = MkEquivalence
    { relation = \xs, ys => xs.coeffs === ys.coeffs
    , reflexive = \_ => Refl
    , symmetric = \xs,ys, prf => sym prf
    , transitive = \xs,ys,zs,prf1,prf2 => trans prf1 prf2
    }
  }

public export
AddBis : {x_set : DecSet} -> (x1, y1 : U x_set) -> (nx1, ny1 : Nat) ->
  (xs, ys : List (U x_set, Nat)) -> (ord : DecOrdering x_set.decOrd.lt x1 y1) ->
  (x_prf : Sorted x_set.decOrd.lt ((x1, nx1) ::: xs)) ->
  (y_prf : Sorted x_set.decOrd.lt ((y1, ny1) ::: ys)) ->
  FreeCarrier x_set

AddBisFront : {x_set : DecSet} -> (x1, y1 : U x_set) -> (nx1, ny1 : Nat) ->
  (xs, ys : List (U x_set, Nat)) -> (ord : DecOrdering x_set.decOrd.lt x1 y1) ->
  (x_prf : Sorted x_set.decOrd.lt ((x1, nx1) ::: xs)) ->
  (y_prf : Sorted x_set.decOrd.lt ((y1, ny1) ::: ys)) ->
  {h : U x_set} -> {nh : Nat} -> {tl : List (U x_set, Nat)} -> 
  {sum_free : Sorted x_set.decOrd.lt ((h, nh) ::: tl)} ->
  (prf : AddBis {x_set} x1 y1 nx1 ny1 xs ys ord x_prf y_prf = MkFreeCarrier {x = x_set} ((h, nh) ::: tl) sum_free) ->
  Either (h = x1) (h = y1)

AddBisFront x1 y1 nx1 ny1 [] [] (Lt pr) x_prf y_prf prf = 
  Left $ sym $ eqHead {x_set} x1 h nx1 nh [(y1, ny1)] tl (SortedCons pr SortedSingle) sum_free ?goal
AddBisFront x1 y1 nx1 ny1 [] [] (Eq pr) x_prf y_prf prf = ?AddBisFront_rhs_7
AddBisFront x1 y1 nx1 ny1 [] [] (Gt pr) x_prf y_prf prf = ?AddBisFront_rhs_8
AddBisFront x1 y1 nx1 ny1 [] ((y2, ny2) :: ys) ord x_prf y_prf prf = ?AddBisFront_rhs_3
AddBisFront x1 y1 nx1 ny1 ((x2, nx2) :: xs) [] ord x_prf y_prf prf = ?AddBisFront_rhs_4
AddBisFront x1 y1 nx1 ny1 ((x2, nx2) :: xs) ((y2, ny2) :: ys) ord x_prf y_prf prf = ?AddBisFront_rhs_5


AddBis x1 y1 nx1 ny1 [] [] (Lt prf) _ _ = MkFreeCarrier ((x1, nx1) ::: [(y1, ny1)]) $ SortedCons prf $ SortedSingle
AddBis x1 y1 nx1 ny1 [] [] (Eq prf) _ _ = MkFreeCarrier ((x1, nx1 + ny1) ::: []) $ SortedSingle
AddBis x1 y1 nx1 ny1 [] [] (Gt prf) _ _ = MkFreeCarrier ((y1, ny1) ::: [(x1, nx1)]) $ SortedCons prf $ SortedSingle

-- TODO: factorize the rest once I dealt with base case in AddBisFront
AddBis x1 y1 nx1 ny1 [] ((y2, ny2) :: ys) (Lt prf) _ y_prf = 
  MkFreeCarrier ((x1, nx1) ::: (y1, ny1) :: (y2, ny2) :: ys) $ SortedCons prf y_prf
AddBis x1 y1 nx1 ny1 [] ((y2, ny2) :: ys) (Eq prf) _ (SortedCons prf2 prf_tail) = 
  MkFreeCarrier ((y1, nx1 + ny1) ::: (y2, ny2) :: ys) $ SortedCons prf2 prf_tail
AddBis x1 y1 nx1 ny1 [] ((y2, ny2) :: ys) (Gt prf) x_prf (SortedCons prf2 prf_tail)
  with (AddBis x1 y2 nx1 ny2 [] ys (x_set.decOrd.compare x1 y2) x_prf prf_tail) proof prf_h
  _ | MkFreeCarrier ((hd, nhd) ::: tl_coeffs) h_prf = 
    case (AddBisFront x1 y2 nx1 ny2 [] ys (x_set.decOrd.compare x1 y2) x_prf prf_tail prf_h) of
      Left eq => 
        MkFreeCarrier ((y1, ny1) ::: (hd, nhd) :: tl_coeffs) $ 
        SortedCons (rewrite eq in prf) h_prf
      Right eq => 
        MkFreeCarrier ((y1, ny1) ::: (hd, nhd) :: tl_coeffs) $ 
        SortedCons (rewrite eq in prf2) h_prf

AddBis x1 y1 nx1 ny1 ((x2, nx2) :: xs) [] (Lt prf) (SortedCons prf2 prf_tail) y_prf
  with (AddBis x2 y1 nx2 ny1 xs [] (x_set.decOrd.compare x2 y1) prf_tail y_prf) proof prf_h
    _ | MkFreeCarrier ((hd, nhd) ::: tl_coeffs) h_prf = 
        case (AddBisFront x2 y1 nx2 ny1 xs [] (x_set.decOrd.compare x2 y1) prf_tail y_prf prf_h) of
          Left eq => 
            MkFreeCarrier ((x1, nx1) ::: (hd, nhd) :: tl_coeffs) $ 
            SortedCons (rewrite eq in prf2) h_prf
          Right eq => 
            MkFreeCarrier ((x1, nx1) ::: (hd, nhd) :: tl_coeffs) $ 
            SortedCons (rewrite eq in prf) h_prf
AddBis x1 y1 nx1 ny1 ((x2, nx2) :: xs) [] (Eq prf) (SortedCons prf2 prf_tail) _ =
  MkFreeCarrier ((x1, nx1 + ny1) ::: (x2, nx2) :: xs) $ SortedCons prf2 prf_tail
AddBis x1 y1 nx1 ny1 ((x2, nx2) :: xs) [] (Gt prf) x_prf _ =
  MkFreeCarrier ((y1, ny1) ::: (x1, nx1) :: (x2, nx2) :: xs) $ SortedCons prf x_prf

AddBis x1 y1 nx1 ny1 ((x2, nx2) :: xs) ((y2, ny2) :: ys) (Lt prf) (SortedCons prf2 prf_tail) y_prf
  with (AddBis x2 y1 nx2 ny1 xs ((y2, ny2) :: ys) (x_set.decOrd.compare x2 y1) prf_tail y_prf) proof prf_h
    _ | MkFreeCarrier ((hd, nhd) ::: tl_coeffs) h_prf = 
        case (AddBisFront x2 y1 nx2 ny1 xs ((y2, ny2) :: ys) (x_set.decOrd.compare x2 y1) prf_tail y_prf prf_h) of
          Left eq => 
            MkFreeCarrier ((x1, nx1) ::: (hd, nhd) :: tl_coeffs) $ 
            SortedCons (rewrite eq in prf2) h_prf
          Right eq => 
            MkFreeCarrier ((x1, nx1) ::: (hd, nhd) :: tl_coeffs) $ 
            SortedCons (rewrite eq in prf) h_prf
AddBis x1 y1 nx1 ny1 ((x2, nx2) :: xs) ((y2, ny2) :: ys) (Eq prf) (SortedCons x1_lt_x2 prf_xs) (SortedCons y1_lt_y2 prf_ys)
  with (AddBis x2 y2 nx2 ny2 xs ys (x_set.decOrd.compare x2 y2) prf_xs prf_ys) proof prf_h
    _ | MkFreeCarrier ((hd, nhd) ::: tl_coeffs) h_prf = 
        case (AddBisFront x2 y2 nx2 ny2 xs ys (x_set.decOrd.compare x2 y2) prf_xs prf_ys prf_h) of
          Left eq => 
            MkFreeCarrier ((x1, nx1) ::: (hd, nhd) :: tl_coeffs) $ 
            SortedCons (rewrite eq in x1_lt_x2) h_prf
          Right eq => 
            MkFreeCarrier ((x1, nx1) ::: (hd, nhd) :: tl_coeffs) $ 
            SortedCons (rewrite eq in rewrite prf in y1_lt_y2) h_prf
AddBis x1 y1 nx1 ny1 ((x2, nx2) :: xs) ((y2, ny2) :: ys) (Gt prf) x_prf (SortedCons prf2 prf_tail)
  with (AddBis x1 y2 nx1 ny2 ((x2, nx2) :: xs) ys (x_set.decOrd.compare x1 y2) x_prf prf_tail) proof prf_h
  _ | MkFreeCarrier ((hd, nhd) ::: tl_coeffs) h_prf = 
    case (AddBisFront x1 y2 nx1 ny2 ((x2, nx2) :: xs) ys (x_set.decOrd.compare x1 y2) x_prf prf_tail prf_h) of
      Left eq => 
        MkFreeCarrier ((y1, ny1) ::: (hd, nhd) :: tl_coeffs) $ 
        SortedCons (rewrite eq in prf) h_prf
      Right eq => 
        MkFreeCarrier ((y1, ny1) ::: (hd, nhd) :: tl_coeffs) $ 
        SortedCons (rewrite eq in prf2) h_prf


public export
Add : {x_set : DecSet} -> FreeCarrier x_set -> FreeCarrier x_set -> FreeCarrier x_set
Add {x_set} (MkFreeCarrier ((x1, nx1) ::: xs) x_prf) (MkFreeCarrier ((y1, ny1) ::: ys) y_prf) =
  AddBis x1 y1 nx1 ny1 xs ys (x_set.decOrd.compare x1 y1) x_prf y_prf


public export
AddHomomorphism : {x : DecSet} ->
  SetoidHomomorphism (FreeSetoid x `Pair` FreeSetoid x) (FreeSetoid x) (Prelude.uncurry Add)
AddHomomorphism x y z = believe_me "AddHomomorphism"

-- AddHomomorphism (xs1, ys1) (xs2, ys2) (MkAnd xs1_eq_xs2 ys1_eq_ys2) i = 
--   ?add_homo

public export
FreeCommutativeSemigroupStructureOver : (x : DecSet) -> CommutativeSemigroupStructure
FreeCommutativeSemigroupStructureOver x = MkSetoidAlgebra
  { algebra = MkAlgebra (FreeCarrier x) $ \Product => Add
  , equivalence = (FreeSetoid x).equivalence
  , congruence = \case
      MkOp Product => \ [xs1,ys1],[xs2,ys2],prf => 
          AddHomomorphism (xs1,ys1) (xs2,ys2) (MkAnd (prf 0) (prf 1))
  }

public export
AddAssociative : {x : DecSet} -> (xs, ys, zs : FreeCarrier x) ->
  (FreeSetoid x).equivalence.relation
    (Add xs (Add ys zs))
    (Add (Add xs ys) zs)


public export
AddCommutative : {x : DecSet} -> (xs, ys : FreeCarrier x) ->
  (FreeSetoid x).equivalence.relation
    (Add xs ys)
    (Add ys xs)


public export
FreeValidatesAxioms : (x : DecSet) -> 
  Validates CommutativeSemigroupTheory (FreeCommutativeSemigroupStructureOver x)
FreeValidatesAxioms x (Sem Associativity) env = AddAssociative (env 0) (env 1) (env 2)
FreeValidatesAxioms x Commutativity env = AddCommutative (env 0) (env 1)


public export
Model : (x : DecSet) -> CommutativeSemigroup
Model x = MkModel
  { Algebra = FreeCommutativeSemigroupStructureOver x
  , Validate = FreeValidatesAxioms x
  }

public export
unit : (x : DecSet) -> Fin n -> FreeCarrier x

public export
FreeCommutativeSemigroupOver : (x : DecSet) -> CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)
FreeCommutativeSemigroupOver x = MkModelOver
  { Model = Model x
  , Env = mate $ unit x
  }

----------------------------------------------- FREENESS PROOF ----------------------------------------------

public export
FreeExtenderFunction : {x : DecSet} -> ExtenderFunction (FreeCommutativeSemigroupOver x)

public export
FreeExtenderSetoidHomomorphism : {x : DecSet} -> ExtenderSetoidHomomorphism (FreeCommutativeSemigroupOver x)
FreeExtenderSetoidHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderFunction other
  , homomorphic = \xs,ys,prf => believe_me "FreeExtenderSetoidHomomorphism"
  }

public export
extenderPreservesPlus : {x : DecSet} -> (other : CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model x).Algebra other.Model.Algebra (FreeExtenderFunction other) Plus
extenderPreservesPlus other xs = believe_me "extenderPreservesPlus"

public export
FreeExtenderHomomorphism : {x : DecSet} -> ExtenderAlgebraHomomorphism (FreeCommutativeSemigroupOver x)
FreeExtenderHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderSetoidHomomorphism other
  , preserves = \case
      MkOp Product => extenderPreservesPlus other
  }

public export
extenderIsMorphism : {x : DecSet} -> (other : CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)) ->
  PreservesEnv (FreeCommutativeSemigroupOver x) other (FreeExtenderSetoidHomomorphism other)
extenderIsMorphism other x = believe_me "extenderIsMorphism"

public export
Extender : {x : DecSet} -> Extender (FreeCommutativeSemigroupOver x)
Extender other = MkHomomorphism
  { H = FreeExtenderHomomorphism other
  , preserves = extenderIsMorphism other
  }

public export
uniqueExtender : {x : DecSet} -> (other : CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)) ->
   (extend : FreeCommutativeSemigroupOver x ~> other) -> (xs : U (Model x)) ->
   other.Model.rel (extend.H.H.H xs)
                   (FreeExtenderFunction other xs)
uniqueExtender other extend xs = believe_me "uniqueExtender"

public export
Uniqueness : {x : DecSet} -> Uniqueness (FreeCommutativeSemigroupOver x)
Uniqueness other extend1 extend2 xs =
  CalcWith (cast other.Model) $
  |~ extend1.H.H.H xs
  ~~ FreeExtenderFunction other xs ...(uniqueExtender other extend1 xs)
  ~~ extend2.H.H.H xs              ..<(uniqueExtender other extend2 xs)

public export
Free : {x : DecSet} -> Free CommutativeSemigroupTheory (cast $ Fin n)
Free = MkFree
  { Data = FreeCommutativeSemigroupOver x
  , UP   = IsFree
    { Exists = Extender
    , Unique = Uniqueness
    }
  }