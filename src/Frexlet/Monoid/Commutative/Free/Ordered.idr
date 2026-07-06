||| An inductive construction of the free commutative monoid over an
||| ordered setoid.
module Frexlet.Monoid.Commutative.Free.Ordered

import Frex

import Frexlet.Monoid.Commutative.Theory
import Frexlet.Monoid.Commutative.Notation.Core

import Data.Order

import Data.Setoid
import Data.Setoid.List
import Data.Setoid.Pair

%default total
%hide Control.Relation.Rel

public export
data Sorted : (lt : Rel a) -> List (a, Nat) -> Type where
  SortedNil    : {lt : Data.Relation.Rel a} -> Sorted lt []
  SortedSingle : {lt : Rel a} -> {x : a} -> {nx : Nat} -> Sorted lt [(x, nx)]
  SortedCons   : {lt : Rel a} -> {x, y : a} -> {nx, ny : Nat} -> {ys : List (a, Nat)} -> 
                lt x y -> Sorted lt ((y, ny) :: ys) -> Sorted lt ((x, nx) :: (y, ny) :: ys)
  

public export
record FreeCarrier (x_set : OrdSetoid) where
  constructor MkFreeCarrier
  coeffs : List (U x_set, Nat)
  sorted : Sorted x_set.decOrd.lt coeffs

public export
NatSetoid : Setoid
NatSetoid = cast Nat
  
public export
FreeSetoid : (x_set : OrdSetoid) -> Setoid
FreeSetoid x_set = MkSetoid
  { U = FreeCarrier x_set
  , equivalence  = MkEquivalence
    { relation   = \xs, ys => (Pair x_set.setoid NatSetoid).ListEquality xs.coeffs ys.coeffs
    , reflexive  = \xs => (Pair x_set.setoid NatSetoid).ListEqualityReflexive xs.coeffs
    , symmetric  = \_,_, prf => (Pair x_set.setoid NatSetoid).ListEqualitySymmetric _ _ prf
    , transitive = \_,_,_,prf1,prf2 => (Pair x_set.setoid NatSetoid).ListEqualityTransitive _ _ _ prf1 prf2
    }
  }


public export
AddList : {x_set : OrdSetoid} -> (xs, ys : List (U x_set, Nat)) -> List (U x_set, Nat)
AddList [] ys = ys
AddList xs [] = xs
AddList ((x1, nx1) :: []) ((y1, ny1) :: []) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = [(x1, nx1), (y1, ny1)]
  _ | Eq _ = [(x1, nx1 + ny1)]
  _ | Gt _ = [(y1, ny1), (x1, nx1)]
AddList ((x1, nx1) :: []) ((y1, ny1) :: ((y2, ny2) :: ys)) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = (x1, nx1) :: (y1, ny1) :: (y2, ny2) :: ys
  _ | Eq _ = (x1, nx1 + ny1) :: (y2, ny2) :: ys
  _ | Gt _ with (assert_total $ AddList [(x1, nx1)] ((y2, ny2) :: ys)) 
    _ | [] = [] -- NB: impossible
    _ | (h :: hs) = (y1, ny1) :: h :: hs 
AddList ((x1, nx1) :: ((x2, nx2) :: xs)) ((y1, ny1) :: []) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (assert_total $ AddList ((x2, nx2) :: xs) [(y1, ny1)]) 
    _ | [] = [] -- NB: impossible
    _ | (h :: hs) = (x1, nx1) :: h :: hs 
  _ | Eq _ = (x1, nx1 + ny1) :: (x2, nx2) :: xs
  _ | Gt _ = (y1, ny1) :: (x1, nx1) :: (x2, nx2) :: xs
AddList ((x1, nx1) :: ((x2, nx2) :: xs)) ((y1, ny1) :: ((y2, ny2) :: ys)) with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (assert_total $ AddList ((x2, nx2) :: xs) ((y1, ny1) :: (y2, ny2) :: ys))
    _ | [] = [] -- NB: impossible
    _ | (h :: hs) = (x1, nx1) :: h :: hs 
  _ | Eq _ with (assert_total $ AddList ((x2, nx2) :: xs) ((y2, ny2) :: ys))
    _ | [] = [] -- NB: impossible
    _ | (h :: hs) = (x1, nx1 + nx2) :: h :: hs 
  _ | Gt _ with (assert_total $ AddList ((x1, nx1) :: (x2, nx2) :: xs) ((y2, ny2) :: ys))
    _ | [] = [] -- NB: impossible
    _ | (h :: hs) = (y1, ny1) :: h :: hs

public export
eqHead : {x, y : _} -> {nx, ny : _} -> {xs, ys : List _} ->   
  (prf : (x, nx) :: xs = (y, ny) :: ys) -> x = y
eqHead Refl = Refl

public export
AddListHead : {x_set : OrdSetoid} -> (x1, y1 : U x_set) -> (nx1, ny1 : Nat) ->
  (xs, ys : List (U x_set, Nat)) ->
  {h : U x_set} -> {nh : Nat} -> {hs : List (U x_set, Nat)} ->
  (prf : AddList {x_set} ((x1, nx1) :: xs) ((y1, ny1) :: ys) = (h, nh) :: hs) ->
  Either (h = x1) (h = y1)
AddListHead x1 y1 nx1 ny1 [] [] prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = Left $ sym $ eqHead prf
  _ | Eq _ = Left $ sym $ eqHead prf
  _ | Gt _ = Right $ sym $ eqHead prf
AddListHead x1 y1 nx1 ny1 [] ((y2, ny2) :: ys) prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ = Left $ sym $ eqHead prf
  _ | Eq _ = Left $ sym $ eqHead prf
  _ | Gt _ with (AddList ((x1, nx1) :: []) ((y2, ny2) :: ys))
    _ | _ :: _ = Right $ sym $ eqHead prf
AddListHead x1 y1 nx1 ny1 ((x2, nx2) :: xs) [] prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (AddList ((x2, nx2) :: xs) ((y1, ny1) :: []))
    _ | _ :: _ = Left $ sym $ eqHead prf
  _ | Eq _ = Left $ sym $ eqHead prf
  _ | Gt _ = Right $ sym $ eqHead prf
AddListHead x1 y1 nx1 ny1 ((x2, nx2) :: xs) ((y2, ny2) :: ys) prf with (x_set.decOrd.compare x1 y1)
  _ | Lt _ with (AddList ((x2, nx2) :: xs) ((y1, ny1) :: (y2, ny2) :: ys))
    _ | _ :: _ = Left $ sym $ eqHead prf
  _ | Eq _ with (AddList ((x2, nx2) :: xs) ((y2, ny2) :: ys))
    _ | _ :: _ = Left $ sym $ eqHead prf
  _ | Gt _ with (AddList ((x1, nx1) :: (x2, nx2) :: xs) ((y2, ny2) :: ys))
    _ | _ :: _ = Right $ sym $ eqHead prf

public export
AddListSorted : {x_set : OrdSetoid} -> (xs, ys : List (U x_set, Nat)) ->
  (prf_xs : Sorted x_set.decOrd.lt xs) ->
  (prf_ys : Sorted x_set.decOrd.lt ys) ->
  Sorted x_set.decOrd.lt (AddList {x_set} xs ys)
AddListSorted [] ys prf_xs prf_ys = prf_ys
AddListSorted (x :: xs) [] prf_xs prf_ys = prf_xs
AddListSorted ((x1, nx1) :: []) ((y1, ny1) :: []) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf = SortedCons prf prf_ys
  _ | Eq prf = SortedSingle
  _ | Gt prf = SortedCons prf prf_xs
AddListSorted ((x1, nx1) :: []) ((y1, ny1) :: ((y2, ny2) :: ys)) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf = SortedCons prf prf_ys
  _ | Eq prf with (prf_ys)
    _ | SortedCons prf' prf_tail = SortedCons (rewrite prf in prf') prf_tail
  _ | Gt prf with (AddList [(x1, nx1)] ((y2, ny2) :: ys)) proof prf_ih
    _ | [] = SortedNil -- NB: impossible
    _ | (h, nh) :: hs with (AddListHead x1 y2 nx1 ny2 [] ys prf_ih) | (prf_ys)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) :: []) ((y2, ny2) :: ys) prf_xs prf_tail
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) :: []) ((y2, ny2) :: ys) prf_xs prf_tail
AddListSorted ((x1, nx1) :: ((x2, nx2) :: xs)) ((y1, ny1) :: []) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf with (AddList ((x2, nx2) :: xs) ((y1, ny1) :: [])) proof prf_ih
    _ | [] = SortedNil -- NB: impossible
    _ | ((h, nh) :: hs) with (AddListHead x2 y1 nx2 ny1 xs [] prf_ih) | (prf_xs)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) :: xs) ((y1, ny1) :: []) prf_tail prf_ys
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) :: xs) ((y1, ny1) :: []) prf_tail prf_ys
  _ | Eq prf with (prf_xs)
    _ | SortedCons prf' prf_tail = SortedCons prf' prf_tail
  _ | Gt prf = SortedCons prf prf_xs
AddListSorted ((x1, nx1) :: ((x2, nx2) :: xs)) ((y1, ny1) :: ((y2, ny2) :: ys)) prf_xs prf_ys with (x_set.decOrd.compare x1 y1)
  _ | Lt prf with (AddList ((x2, nx2) :: xs) ((y1, ny1) :: ((y2, ny2) :: ys))) proof prf_ih
    _ | [] = SortedNil -- NB: impossible
    _ | ((h, nh) :: hs) with (AddListHead x2 y1 nx2 ny1 xs ((y2, ny2) :: ys) prf_ih) | (prf_xs)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) :: xs) ((y1, ny1) :: ((y2, ny2) :: ys)) prf_tail prf_ys
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) :: xs) ((y1, ny1) :: ((y2, ny2) :: ys)) prf_tail prf_ys
  _ | Eq prf with (AddList ((x2, nx2) :: xs) ((y2, ny2) :: ys)) proof prf_ih
    _ | [] = SortedNil -- NB: impossible
    _ | ((h, nh) :: hs) with (AddListHead x2 y2 nx2 ny2 xs ys prf_ih)
      _ | Left eq with (prf_xs) | (prf_ys)
        _ | SortedCons prf1 prf_tail1 | SortedCons prf2 prf_tail2 = SortedCons (rewrite eq in prf1) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) :: xs) ((y2, ny2) :: ys) prf_tail1 prf_tail2
      _ | Right eq with (prf_xs) | (prf_ys)
        _ | SortedCons prf1 prf_tail1 | SortedCons prf2 prf_tail2 = SortedCons (rewrite eq in rewrite prf in prf2) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x2, nx2) :: xs) ((y2, ny2) :: ys) prf_tail1 prf_tail2
  _ | Gt prf with (AddList ((x1, nx1) :: ((x2, nx2) :: xs)) ((y2, ny2) :: ys)) proof prf_ih
    _ | [] = SortedNil -- NB: impossible
    _ | ((h, nh) :: hs) with (AddListHead x1 y2 nx1 ny2 ((x2, nx2) :: xs) ys prf_ih) | (prf_ys)
      _ | Left eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf) $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) :: ((x2, nx2) :: xs)) ((y2, ny2) :: ys) prf_xs prf_tail
      _ | Right eq | SortedCons prf' prf_tail = SortedCons (rewrite eq in prf') $
          rewrite sym prf_ih in assert_total $ AddListSorted ((x1, nx1) :: ((x2, nx2) :: xs)) ((y2, ny2) :: ys) prf_xs prf_tail


public export
Add : {x_set : OrdSetoid} -> FreeCarrier x_set -> FreeCarrier x_set -> FreeCarrier x_set
Add {x_set} (MkFreeCarrier xs x_prf) (MkFreeCarrier ys y_prf) = 
  MkFreeCarrier (AddList xs ys) (AddListSorted xs ys x_prf y_prf)

public export
Neutral : {x_set : OrdSetoid} -> FreeCarrier x_set
Neutral = MkFreeCarrier [] SortedNil

public export
AddHomomorphism : {x_set : OrdSetoid} ->
  SetoidHomomorphism (FreeSetoid x_set `Pair` FreeSetoid x_set) (FreeSetoid x_set) (Prelude.uncurry Add)
AddHomomorphism x y z = believe_me "AddHomomorphism"


public export
FreeCommutativeMonoidStructureOver : (x_set : OrdSetoid) -> MonoidStructure
FreeCommutativeMonoidStructureOver x_set = MkSetoidAlgebra
  { algebra = MkAlgebra (FreeCarrier x_set) $ \case
    Product => Add
    Neutral => Neutral
  , equivalence = (FreeSetoid x_set).equivalence
  , congruence = \case
      MkOp Product => \ [xs1,ys1],[xs2,ys2],prf => 
          AddHomomorphism (xs1,ys1) (xs2,ys2) (MkAnd (prf 0) (prf 1))
      MkOp Neutral => \[],[],prf => (FreeSetoid x_set).equivalence.reflexive _
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
LftNeutrality : {x_set : OrdSetoid} -> (xs : FreeCarrier x_set) ->
  (FreeSetoid x_set).equivalence.relation
    (Add Neutral xs)
    xs
LftNeutrality (MkFreeCarrier coeffs _) = 
  (Pair x_set.setoid NatSetoid).ListEqualityReflexive _

public export
RgtNeutrality : {x_set : OrdSetoid} -> (xs : FreeCarrier x_set) ->
  (FreeSetoid x_set).equivalence.relation
    (Add xs Neutral)
    xs
RgtNeutrality (MkFreeCarrier [] _) =
  (Pair x_set.setoid NatSetoid).ListEqualityReflexive _
RgtNeutrality (MkFreeCarrier (x :: xs) _) =
  (Pair x_set.setoid NatSetoid).ListEqualityReflexive _

public export
FreeValidatesAxioms : (x_set : OrdSetoid) -> 
  Validates CommutativeMonoidTheory (FreeCommutativeMonoidStructureOver x_set)
FreeValidatesAxioms _ (Mon Associativity) env = AddAssociative (env 0) (env 1) (env 2)
FreeValidatesAxioms _ (Mon LftNeutrality) env = LftNeutrality (env 0)
FreeValidatesAxioms _ (Mon RgtNeutrality) env = RgtNeutrality (env 0)
FreeValidatesAxioms _ Commutativity env = AddCommutative (env 0) (env 1)


public export
Model : (x_set : OrdSetoid) -> CommutativeMonoid
Model x_set = MkModel
  { Algebra = FreeCommutativeMonoidStructureOver x_set
  , Validate = FreeValidatesAxioms x_set
  }

public export
unit : (x_set : OrdSetoid) -> x_set.setoid ~> FreeSetoid x_set
unit x_set = MkSetoidHomomorphism
  { H = \y => MkFreeCarrier ((y, 0) :: []) SortedSingle
  , homomorphic = \x, y, prf => MkAnd prf Refl :: Nil
  }

public export
FreeCommutativeMonoidOver : (x_set : OrdSetoid) -> CommutativeMonoidTheory `ModelOver` (cast x_set)
FreeCommutativeMonoidOver x_set = MkModelOver
  { Model = Model x_set
  , Env = unit x_set
  }

----------------------------------------------- FREENESS PROOF ----------------------------------------------


public export
FreeExtenderFunction : {x_set : OrdSetoid} -> ExtenderFunction (FreeCommutativeMonoidOver x_set)
FreeExtenderFunction other (MkFreeCarrier xs _) = 
  other.Model.sum $ map (\(x, nx) => mult other.Model (S nx) (other.Env.H x)) (fromList xs)

public export
FreeExtenderSetoidHomomorphism : {x_set : OrdSetoid} -> ExtenderSetoidHomomorphism (FreeCommutativeMonoidOver x_set)
FreeExtenderSetoidHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderFunction other
  , homomorphic = \xs,ys,prf => believe_me "FreeExtenderSetoidHomomorphism"
  }

public export
extenderPreservesPlus : {x_set : OrdSetoid} -> (other : CommutativeMonoidTheory `ModelOver` (cast x_set)) ->
  Preserves (Model x_set).Algebra other.Model.Algebra (FreeExtenderFunction other) Plus
extenderPreservesPlus other xs = believe_me "extenderPreservesPlus"

public export
extenderPreservesZero : {x_set : OrdSetoid} -> (other : CommutativeMonoidTheory `ModelOver` (cast x_set)) ->
  Preserves (Model x_set).Algebra other.Model.Algebra (FreeExtenderFunction other) Zero
extenderPreservesZero other [] = other.Model.equivalence.reflexive _

public export
FreeExtenderHomomorphism : {x_set : OrdSetoid} -> ExtenderAlgebraHomomorphism (FreeCommutativeMonoidOver x_set)
FreeExtenderHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderSetoidHomomorphism other
  , preserves = \case
      MkOp Product => extenderPreservesPlus other
      MkOp Neutral => extenderPreservesZero other
  }

public export
extenderIsMorphism : {x_set : OrdSetoid} -> (other : CommutativeMonoidTheory `ModelOver` (cast x_set)) ->
  PreservesEnv (FreeCommutativeMonoidOver x_set) other (FreeExtenderSetoidHomomorphism other)
extenderIsMorphism other x = believe_me "extenderIsMorphism"


public export
Extender : {x_set : OrdSetoid} -> Extender (FreeCommutativeMonoidOver x_set)
Extender other = MkHomomorphism
  { H = FreeExtenderHomomorphism other
  , preserves = extenderIsMorphism other
  } 

public export
uniqueExtender : {x_set : OrdSetoid} -> (other : CommutativeMonoidTheory `ModelOver` (cast x_set)) ->
  (extend : FreeCommutativeMonoidOver x_set ~> other) -> (xs : U (Model x_set)) ->
  other.Model.rel (extend.H.H.H xs)
                  (FreeExtenderFunction other xs)
uniqueExtender other extend xs = believe_me "uniqueExtender"

public export
Uniqueness : {x_set : OrdSetoid} -> Uniqueness (FreeCommutativeMonoidOver x_set)
Uniqueness other extend1 extend2 xs =
  CalcWith (cast other.Model) $
  |~ extend1.H.H.H xs
  ~~ FreeExtenderFunction other xs ...(uniqueExtender other extend1 xs)
  ~~ extend2.H.H.H xs              ..<(uniqueExtender other extend2 xs)

public export
Free : (x_set : OrdSetoid) -> Free CommutativeMonoidTheory (cast x_set)
Free x_set = MkFree
  { Data = FreeCommutativeMonoidOver x_set
  , UP   = IsFree
    { Exists = Extender
    , Unique = Uniqueness
    }
  }