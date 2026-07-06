module Frexlet.Semigroup.Commutative.Free

import Frex

import Frexlet.Semigroup.Commutative.Theory
import Frexlet.Semigroup.Commutative.Dirac
import Frexlet.Semigroup.Commutative.Notation.Core

import Data.Vect
import Data.List1

import Data.Order

import Data.Setoid
import Data.Setoid.List1
import Data.Setoid.Pair

import Decidable.Equality
import Decidable.Decidable

%default total
%hide Control.Relation.Rel

public export
data Sorted : (lt : Rel a) -> List1 (a, Nat) -> Type where
  SortedSingle : {lt : Rel a} -> {x : a} -> {nx : Nat} -> Sorted lt ((x, nx) ::: [])
  SortedCons   : {lt : Rel a} -> {x, y : a} -> {nx, ny : Nat} -> {ys : List (a, Nat)} -> 
                 lt x y -> Sorted lt ((y, ny) ::: ys) -> Sorted lt ((x, nx) ::: (y, ny) :: ys)
  

public export
record FreeCarrier (x_set : OrdSetoid) where
  constructor MkFreeCarrier
  coeffs : List1 (U x_set, Nat)
  sorted : Sorted x_set.decOrd.lt coeffs

public export
NatSetoid : Setoid
NatSetoid = cast Nat
  
public export
FreeSetoid : (x_set : OrdSetoid) -> Setoid
FreeSetoid x_set = MkSetoid
  { U = FreeCarrier x_set
  , equivalence  = MkEquivalence
    { relation   = \xs, ys => (Pair x_set.setoid NatSetoid).List1Equality xs.coeffs ys.coeffs
    , reflexive  = \xs => (Pair x_set.setoid NatSetoid).List1EqualityReflexive xs.coeffs
    , symmetric  = \_,_, prf => (Pair x_set.setoid NatSetoid).List1EqualitySymmetric _ _ prf
    , transitive = \_,_,_,prf1,prf2 => (Pair x_set.setoid NatSetoid).List1EqualityTransitive _ _ _ prf1 prf2
    }
  }


public export
AddList : {x_set : OrdSetoid} -> (xs, ys : List1 (U x_set, Nat)) -> List1 (U x_set, Nat)
AddList ((x1, nx1) ::: []) ((y1, ny1) ::: []) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = (x1, nx1) ::: [(y1, ny1)]
  _ | Eq _ = (x1, nx1 + ny1) ::: []
  _ | Gt _ = (y1, ny1) ::: [(x1, nx1)]
AddList ((x1, nx1) ::: []) ((y1, ny1) ::: ((y2, ny2) :: ys)) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = (x1, nx1) ::: (y1, ny1) :: (y2, ny2) :: ys
  _ | Eq _ = (x1, nx1 + ny1) ::: (y2, ny2) :: ys
  _ | Gt _ with (assert_total $ AddList ((x1, nx1) ::: []) ((y2, ny2) ::: ys))
    _ | (h ::: hs) = (y1, ny1) ::: h :: hs 
AddList ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y1, ny1) ::: []) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (assert_total $ AddList ((x2, nx2) ::: xs) ((y1, ny1) ::: []))
    _ | (h ::: hs) = (x1, nx1) ::: h :: hs
  _ | Eq _ = (x1, nx1 + ny1) ::: (x2, nx2) :: xs
  _ | Gt _ = (y1, ny1) ::: (x1, nx1) :: (x2, nx2) :: xs
AddList ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y1, ny1) ::: ((y2, ny2) :: ys)) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (assert_total $ AddList ((x2, nx2) ::: xs) ((y1, ny1) ::: (y2, ny2) :: ys))
    _ | (h ::: hs) = (x1, nx1) ::: h :: hs
  _ | Eq _ with (assert_total $ AddList ((x2, nx2) ::: xs) ((y2, ny2) ::: ys))
    _ | (h ::: hs) = (x1, nx1 + ny1) ::: h :: hs
  _ | Gt _ with (assert_total $ AddList ((x1, nx1) ::: (x2, nx2) :: xs) ((y2, ny2) ::: ys))
    _ | (h ::: hs) = (y1, ny1) ::: h :: hs

public export
eqHead : {x, y : _} -> {nx, ny : _} -> {xs, ys : List _} ->   
  (prf : (x, nx) ::: xs = (y, ny) ::: ys) -> x = y
eqHead Refl = Refl

public export
AddListHead : {x_set : OrdSetoid} -> (x1, y1 : U x_set) -> (nx1, ny1 : Nat) ->
  (xs, ys : List (U x_set, Nat)) ->
  {h : U x_set} -> {nh : Nat} -> {hs : List (U x_set, Nat)} ->
  (prf : AddList {x_set} ((x1, nx1) ::: xs) ((y1, ny1) ::: ys) = (h, nh) ::: hs) ->
  Either (h = x1) (h = y1)
AddListHead x1 y1 nx1 ny1 [] [] prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = Left $ sym $ eqHead prf
  _ | Eq _ = Left $ sym $ eqHead prf
  _ | Gt _ = Right $ sym $ eqHead prf
AddListHead x1 y1 nx1 ny1 [] ((y2, ny2) :: ys) prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = Left $ sym $ eqHead prf
  _ | Eq _ = Left $ sym $ eqHead prf
  _ | Gt _ with (AddList ((x1, nx1) ::: []) ((y2, ny2) ::: ys))
    _ | _ ::: _ = Right $ sym $ eqHead prf
AddListHead x1 y1 nx1 ny1 ((x2, nx2) :: xs) [] prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (AddList ((x2, nx2) ::: xs) ((y1, ny1) ::: []))
    _ | _ ::: _ = Left $ sym $ eqHead prf
  _ | Eq _ = Left $ sym $ eqHead prf
  _ | Gt _ = Right $ sym $ eqHead prf
AddListHead x1 y1 nx1 ny1 ((x2, nx2) :: xs) ((y2, ny2) :: ys) prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (AddList ((x2, nx2) ::: xs) ((y1, ny1) ::: (y2, ny2) :: ys))
    _ | _ ::: _ = Left $ sym $ eqHead prf
  _ | Eq _ with (AddList ((x2, nx2) ::: xs) ((y2, ny2) ::: ys))
    _ | _ ::: _ = Left $ sym $ eqHead prf
  _ | Gt _ with (AddList ((x1, nx1) ::: (x2, nx2) :: xs) ((y2, ny2) ::: ys))
    _ | _ ::: _ = Right $ sym $ eqHead prf

public export
AddListSorted : {x_set : OrdSetoid} -> (xs, ys : List1 (U x_set, Nat)) ->
  (prf_xs : Sorted x_set.decOrd.lt xs) ->
  (prf_ys : Sorted x_set.decOrd.lt ys) ->
  Sorted x_set.decOrd.lt (AddList {x_set} xs ys)
AddListSorted ((x1, nx1) ::: []) ((y1, ny1) ::: []) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf = SortedCons prf prf_ys
  _ | Eq prf = SortedSingle
  _ | Gt prf = SortedCons prf prf_xs
AddListSorted ((x1, nx1) ::: []) ((y1, ny1) ::: ((y2, ny2) :: ys)) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf = SortedCons prf prf_ys
  _ | Eq prf with (prf_ys)
    _ | SortedCons prf' prf_tail = SortedCons (rewrite prf in prf') prf_tail
  _ | Gt prf with (AddList ((x1, nx1) ::: []) ((y2, ny2) ::: ys)) proof prf_ih
    _ | ((h, nh) ::: hs) with (AddListHead x1 y2 nx1 ny2 [] ys prf_ih) | (prf_ys)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) ::: []) ((y2, ny2) ::: ys) prf_xs prf_tail
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) ::: []) ((y2, ny2) ::: ys) prf_xs prf_tail
AddListSorted ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y1, ny1) ::: []) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf with (AddList ((x2, nx2) ::: xs) ((y1, ny1) ::: [])) proof prf_ih
    _ | ((h, nh) ::: hs) with (AddListHead x2 y1 nx2 ny1 xs [] prf_ih) | (prf_xs)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) ::: xs) ((y1, ny1) ::: []) prf_tail prf_ys
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) ::: xs) ((y1, ny1) ::: []) prf_tail prf_ys
  _ | Eq prf with (prf_xs)
    _ | SortedCons prf' prf_tail = SortedCons prf' prf_tail
  _ | Gt prf = SortedCons prf prf_xs
AddListSorted ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y1, ny1) ::: ((y2, ny2) :: ys)) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf with (AddList ((x2, nx2) ::: xs) ((y1, ny1) ::: ((y2, ny2) :: ys))) proof prf_ih
    _ | ((h, nh) ::: hs) with (AddListHead x2 y1 nx2 ny1 xs ((y2, ny2) :: ys) prf_ih) | (prf_xs)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) ::: xs) ((y1, ny1) ::: ((y2, ny2) :: ys)) prf_tail prf_ys
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) ::: xs) ((y1, ny1) ::: ((y2, ny2) :: ys)) prf_tail prf_ys
  _ | Eq prf with (AddList ((x2, nx2) ::: xs) ((y2, ny2) ::: ys)) proof prf_ih
    _ | ((h, nh) ::: hs) with (AddListHead x2 y2 nx2 ny2 xs ys prf_ih)
      _ | Left eq with (prf_xs) | (prf_ys)
        _ | SortedCons prf1 prf_tail1 | SortedCons prf2 prf_tail2 = SortedCons (rewrite eq in prf1) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) ::: xs) ((y2, ny2) ::: ys) prf_tail1 prf_tail2
      _ | Right eq with (prf_xs) | (prf_ys)
        _ | SortedCons prf1 prf_tail1 | SortedCons prf2 prf_tail2 = SortedCons (rewrite eq in rewrite prf in prf2) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) ::: xs) ((y2, ny2) ::: ys) prf_tail1 prf_tail2
  _ | Gt prf with (AddList ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y2, ny2) ::: ys)) proof prf_ih
    _ | ((h, nh) ::: hs) with (AddListHead x1 y2 nx1 ny2 ((x2, nx2) :: xs) ys prf_ih) | (prf_ys)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y2, ny2) ::: ys) prf_xs prf_tail
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) ::: ((x2, nx2) :: xs)) ((y2, ny2) ::: ys) prf_xs prf_tail


public export
Add : {x_set : OrdSetoid} -> FreeCarrier x_set -> FreeCarrier x_set -> FreeCarrier x_set
Add {x_set} (MkFreeCarrier xs x_prf) (MkFreeCarrier ys y_prf) = 
  MkFreeCarrier (AddList xs ys) (AddListSorted xs ys x_prf y_prf)


public export
AddHomomorphism : {x_set : OrdSetoid} ->
  SetoidHomomorphism (FreeSetoid x_set `Pair` FreeSetoid x_set) (FreeSetoid x_set) (Prelude.uncurry Add)
AddHomomorphism x y z = believe_me "AddHomomorphism"

-- AddHomomorphism (xs1, ys1) (xs2, ys2) (MkAnd xs1_eq_xs2 ys1_eq_ys2) i = 
--   ?add_homo

public export
FreeCommutativeSemigroupStructureOver : (x_set : OrdSetoid) -> CommutativeSemigroupStructure
FreeCommutativeSemigroupStructureOver x_set = MkSetoidAlgebra
  { algebra = MkAlgebra (FreeCarrier x_set) $ \Product => Add
  , equivalence = (FreeSetoid x_set).equivalence
  , congruence = \case
      MkOp Product => \ [xs1,ys1],[xs2,ys2],prf => 
          AddHomomorphism (xs1,ys1) (xs2,ys2) (MkAnd (prf 0) (prf 1))
  }

public export
AddAssociative : {x_set : OrdSetoid} -> (xs, ys, zs : FreeCarrier x_set) ->
  (FreeSetoid x_set).equivalence.relation
    (Add xs (Add ys zs))
    (Add (Add xs ys) zs)
AddAssociative xs ys zs = believe_me "AddAssociative"


public export
AddCommutative : {x_set : OrdSetoid} -> (xs, ys : FreeCarrier x_set) ->
  (FreeSetoid x_set).equivalence.relation
    (Add xs ys)
    (Add ys xs)
AddCommutative xs ys = believe_me "AddCommutative"


public export
FreeValidatesAxioms : (x_set : OrdSetoid) -> 
  Validates CommutativeSemigroupTheory (FreeCommutativeSemigroupStructureOver x_set)
FreeValidatesAxioms _ (Sem Associativity) env = AddAssociative (env 0) (env 1) (env 2)
FreeValidatesAxioms _ Commutativity env = AddCommutative (env 0) (env 1)


public export
Model : (x_set : OrdSetoid) -> CommutativeSemigroup
Model x_set = MkModel
  { Algebra = FreeCommutativeSemigroupStructureOver x_set
  , Validate = FreeValidatesAxioms x_set
  }

public export
unit : (x_set : OrdSetoid) -> x_set.setoid ~> FreeSetoid x_set
unit x_set = MkSetoidHomomorphism
  { H = \y => MkFreeCarrier ((y, 0) ::: []) SortedSingle
  , homomorphic = \x, y, prf => MkAnd prf Refl ::: Nil
  }

public export
FreeCommutativeSemigroupOver : (x_set : OrdSetoid) -> CommutativeSemigroupTheory `ModelOver` (cast x_set)
FreeCommutativeSemigroupOver x_set = MkModelOver
  { Model = Model x_set
  , Env = unit x_set
  }

----------------------------------------------- FREENESS PROOF ----------------------------------------------

public export
fromList1 : (xs : List1 a) -> Vect (S $ length $ tail xs) a
fromList1 (x ::: xs) = x :: fromList xs

public export
FreeExtenderFunction : {x_set : OrdSetoid} -> ExtenderFunction (FreeCommutativeSemigroupOver x_set)
FreeExtenderFunction other (MkFreeCarrier xs@(hd ::: tl) _) = 
  other.Model.sum $ map (\(x, nx) => other.Model.mult (S nx) (other.Env.H x)) (fromList1 xs)

public export
FreeExtenderSetoidHomomorphism : {x_set : OrdSetoid} -> ExtenderSetoidHomomorphism (FreeCommutativeSemigroupOver x_set)
FreeExtenderSetoidHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderFunction other
  , homomorphic = \xs,ys,prf => believe_me "FreeExtenderSetoidHomomorphism"
  }

public export
extenderPreservesPlus : {x_set : OrdSetoid} -> (other : CommutativeSemigroupTheory `ModelOver` (cast x_set)) ->
  Preserves (Model x_set).Algebra other.Model.Algebra (FreeExtenderFunction other) Plus
extenderPreservesPlus other xs = believe_me "extenderPreservesPlus"

public export
FreeExtenderHomomorphism : {x_set : OrdSetoid} -> ExtenderAlgebraHomomorphism (FreeCommutativeSemigroupOver x_set)
FreeExtenderHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderSetoidHomomorphism other
  , preserves = \case
      MkOp Product => extenderPreservesPlus other
  }

public export
extenderIsMorphism : {x_set : OrdSetoid} -> (other : CommutativeSemigroupTheory `ModelOver` (cast x_set)) ->
  PreservesEnv (FreeCommutativeSemigroupOver x_set) other (FreeExtenderSetoidHomomorphism other)
extenderIsMorphism other x = believe_me "extenderIsMorphism"

public export
Extender : {x_set : OrdSetoid} -> Extender (FreeCommutativeSemigroupOver x_set)
Extender other = MkHomomorphism
  { H = FreeExtenderHomomorphism other
  , preserves = extenderIsMorphism other
  }

public export
uniqueExtender : {x_set : OrdSetoid} -> (other : CommutativeSemigroupTheory `ModelOver` (cast x_set)) ->
   (extend : FreeCommutativeSemigroupOver x_set ~> other) -> (xs : U (Model x_set)) ->
   other.Model.rel (extend.H.H.H xs)
                   (FreeExtenderFunction other xs)
uniqueExtender other extend xs = believe_me "uniqueExtender"

public export
Uniqueness : {x_set : OrdSetoid} -> Uniqueness (FreeCommutativeSemigroupOver x_set)
Uniqueness other extend1 extend2 xs =
  CalcWith (cast other.Model) $
  |~ extend1.H.H.H xs
  ~~ FreeExtenderFunction other xs ...(uniqueExtender other extend1 xs)
  ~~ extend2.H.H.H xs              ..<(uniqueExtender other extend2 xs)

public export
Free : (x_set : OrdSetoid) -> Free CommutativeSemigroupTheory (cast x_set)
Free x_set = MkFree
  { Data = FreeCommutativeSemigroupOver x_set
  , UP   = IsFree
    { Exists = Extender
    , Unique = Uniqueness
    }
  }