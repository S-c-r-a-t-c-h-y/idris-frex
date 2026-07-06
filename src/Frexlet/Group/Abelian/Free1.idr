module Frexlet.Group.Abelian.Free1

import Frex

import Notation
import Notation.Action

import Frexlet.Group.Abelian.Theory
import Frexlet.Group.Abelian.Notation.Core

import Frexlet.Group.Abelian.Dirac
import Frexlet.Group.Abelian.IntInd

import Syntax.PreorderReasoning.Setoid

import Data.Vect
import Data.Vect.Properties
import Data.Setoid.Vect
import public Data.Vect.Extra
import Data.Vect.Extra1

%default total

{-

public export
add : Vect n IntInd -> Vect n IntInd -> Vect n IntInd
add xs ys = zipWith (+) xs ys

public export
neutral : {n : Nat} -> Vect n IntInd
neutral = replicate n 0

public export
inverse : Vect n IntInd -> Vect n IntInd
inverse xs = map negate xs


IntSetoid : Setoid
IntSetoid = cast IntInd

plusCommutativeInt : (x, y : IntInd) -> x + y = y + x
plusCommutativeInt x y = believe_me $ Refl {x = x + y}

plusAssociativeInt : (x, y, z : IntInd) -> x + (y + z) = (x + y) + z
plusAssociativeInt x y z = believe_me $ Refl {x = x + (y + z)}

plusZeroLeftNeutralInt : (x : IntInd) -> 0 + x = x
plusZeroLeftNeutralInt x = believe_me $ Refl {x}

plusZeroRightNeutralInt : (x : IntInd) -> x + 0 = x
plusZeroRightNeutralInt x = believe_me $ Refl {x}

plusLftInverseInt : (x : IntInd) -> (-x) + x = 0
plusLftInverseInt x = believe_me $ Refl {x = the IntInd 0}


public export
FreeAbelianGroupStructureOver : (n : Nat) -> AbelianGroupStructure
FreeAbelianGroupStructureOver n = MkSetoidAlgebra
  { algebra = MkAlgebra (Vect n IntInd) $ \case
        Mono x => case x of
          Product => add
          Neutral => neutral
        Inverse => inverse
  , equivalence = (VectSetoid n IntSetoid).equivalence
  , congruence = \case
    MkOp (Mono x) => case x of
      Product => \[xs1, xs2], [ys1, ys2], prf, i => 
        CalcWith IntSetoid $
        |~ index i (add xs1 xs2)
        ~~ index i xs1 + index i xs2  ... (zipWithIndexLinear _ _ _ _)
        ~~ index i ys1 + index i ys2  ... (cong2 (+) (prf 0 i) (prf 1 i))
        ~~ index i (add ys1 ys2)      ..< (zipWithIndexLinear _ _ _ _)
      Neutral => \_, _, _, _ => Refl
    MkOp Inverse => \[x], [y], prf, i => 
      CalcWith IntSetoid $
      |~ index i (map negate x)
      ~~ negate (index i x)     ... (indexNaturality _ _ _)
      ~~ negate (index i y)     ... (cong negate (prf 0 i))
      ~~ index i (map negate y) ..< (indexNaturality _ _ _)
  }

public export
AddCommutative : {n : Nat} -> (xs, ys : Vect n IntInd) ->
  (VectSetoid n IntSetoid).equivalence.relation
    (add xs ys)
    (add ys xs)
AddCommutative xs ys i = 
  CalcWith IntSetoid $
  |~ index i (add xs ys)
  ~~ index i xs + index i ys ... (zipWithIndexLinear _ _ _ _)
  ~~ index i ys + index i xs ... (plusCommutativeInt _ _)
  ~~ index i (add ys xs)     ..< (zipWithIndexLinear _ _ _ _)

public export
AddAssociative : {n : Nat} -> (xs, ys, zs : Vect n IntInd) ->
  (VectSetoid n IntSetoid).equivalence.relation
    (add xs (add ys zs))
    (add (add xs ys) zs)
AddAssociative xs ys zs i = 
  CalcWith IntSetoid $
  |~ index i (add xs (add ys zs))
  ~~ index i xs + index i (add ys zs)       ... (zipWithIndexLinear _ _ _ _)
  ~~ index i xs + (index i ys + index i zs) ... (cong2 (+) Refl $ zipWithIndexLinear _ _ _ _)
  ~~ (index i xs + index i ys) + index i zs ... (plusAssociativeInt _ _ _)
  ~~ index i (add xs ys) + index i zs       ..< (cong2 (+) (zipWithIndexLinear _ _ _ _) Refl)
  ~~ index i (add (add xs ys) zs)           ..< (zipWithIndexLinear _ _ _ _)

public export
LftNeutrality : {n : Nat} -> (xs : Vect n IntInd) ->
  (VectSetoid n IntSetoid).equivalence.relation
    (add Free.neutral xs) xs
LftNeutrality xs i = 
  CalcWith IntSetoid $
  |~ index i (add neutral xs)
  ~~ index i neutral + index i xs ... (zipWithIndexLinear _ _ _ _)
  ~~ 0 + index i xs               ... (cong2 (+) (indexReplicate _ _) Refl)
  ~~ index i xs                   ... (plusZeroLeftNeutralInt _)

public export
RgtNeutrality : {n : Nat} -> (xs : Vect n IntInd) ->
  (VectSetoid n IntSetoid).equivalence.relation
    (add xs Free.neutral) xs
RgtNeutrality xs = 
  CalcWith (VectSetoid n IntSetoid) $
  |~ add xs neutral
  ~~ add neutral xs  ... (AddCommutative _ _)
  ~~ xs              ... (LftNeutrality _)

public export
LftInverse : {n : Nat} -> (xs : Vect n IntInd) ->
  (VectSetoid n IntSetoid).equivalence.relation
    (add (inverse xs) xs) Free.neutral
LftInverse xs i =
  CalcWith IntSetoid $
  |~ index i (add (inverse xs) xs)
  ~~ index i (inverse xs) + index i xs ... (zipWithIndexLinear _ _ _ _)
  ~~ (- index i xs) + index i xs       ... (cong2 (+) (indexNaturality _ _ _) Refl)
  ~~ 0                                 ... (plusLftInverseInt _)
  ~~ index i neutral                   ..< (indexReplicate _ _)
  

public export
RgtInverse : {n : Nat} -> (xs : Vect n IntInd) ->
  (VectSetoid n IntSetoid).equivalence.relation
    (add xs (inverse xs)) Free.neutral
RgtInverse xs =
  CalcWith (VectSetoid n IntSetoid) $
  |~ add xs (inverse xs)
  ~~ add (inverse xs) xs ... (AddCommutative _ _)
  ~~ neutral             ... (LftInverse _)

public export
FreeValidatesAxioms : (n : Nat) -> 
  Validates AbelianGroupTheory (FreeAbelianGroupStructureOver n)
FreeValidatesAxioms n (Grp (Mon LftNeutrality)) env = LftNeutrality _
FreeValidatesAxioms n (Grp (Mon RgtNeutrality)) env = RgtNeutrality _
FreeValidatesAxioms n (Grp (Mon Associativity)) env = AddAssociative _ _ _
FreeValidatesAxioms n (Grp LftInverse) env = LftInverse _
FreeValidatesAxioms n (Grp RgtInverse) env = RgtInverse _
FreeValidatesAxioms n Commutativity env = AddCommutative _ _

public export
Model : (n : Nat) -> AbelianGroup
Model n = MkModel
  { Algebra = FreeAbelianGroupStructureOver n
  , Validate = FreeValidatesAxioms n
  }

public export
unit : (n : Nat) -> Fin n -> Vect n IntInd
unit n i = Fin.tabulate $ dirac i

public export
FreeAbelianGroupOver : (n : Nat) -> AbelianGroupTheory `ModelOver` (cast $ Fin n)
FreeAbelianGroupOver n = MkModelOver
  { Model = Model n
  , Env   = mate $ unit n
  }

----------------------------------------------------------------------------------

public export
FreeExtenderFunction : {n : Nat} -> ExtenderFunction (FreeAbelianGroupOver n)
FreeExtenderFunction other =
  let %hint
      notation : Action1 IntInd (U $ other.Model)
      notation = NatAction1 (other.Model)
  in
  other.Model.sum . (mapWithPos (\i,k => k *. other.Env.H i))

public export
FreeExtenderSetoidHomomorphism : {n : Nat} -> ExtenderSetoidHomomorphism (FreeAbelianGroupOver n)
FreeExtenderSetoidHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderFunction other
  , homomorphic = \xs,ys,prf => Data.Setoid.Definition.reflect (cast other.Model)
                              $ cong (FreeExtenderFunction other)
                              $ vectorExtensionality xs ys prf
  }

public export
extenderPreservesPlus : {n : Nat} -> (other : AbelianGroupTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model n).Algebra other.Model.Algebra (FreeExtenderFunction other) (MkOp (Mono Product))

public export
extenderPreservesZero : {n : Nat} -> (other : AbelianGroupTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model n).Algebra other.Model.Algebra (FreeExtenderFunction other) (MkOp (Mono Neutral))

public export
extenderPreservesInverse : {n : Nat} -> (other : AbelianGroupTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model n).Algebra other.Model.Algebra (FreeExtenderFunction other) (MkOp Inverse)


public export
FreeExtenderHomomorphism : {n : Nat} -> ExtenderAlgebraHomomorphism (FreeAbelianGroupOver n)
FreeExtenderHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderSetoidHomomorphism other
  , preserves = \case
    MkOp (Mono x) => case x of
      Product => extenderPreservesPlus other
      Neutral => extenderPreservesZero other
    MkOp Inverse  => extenderPreservesInverse other
  }

public export
extenderIsMorphism : {n : Nat} -> (other : AbelianGroupTheory `ModelOver` (cast $ Fin n)) ->
  PreservesEnv (FreeAbelianGroupOver n) other (FreeExtenderSetoidHomomorphism other)
extenderIsMorphism {n} other x =
  let %hint
      notation : Action1 IntInd (U other.Model)
      notation = NatAction1 other.Model
      %hint
      notation' : Action1 IntInd (U (Model n))
      notation' = NatAction1 (Model n)
      h : U (Model n) -> U other.Model
      h = FreeExtenderFunction other
  in
  ?extenderIsMorphism_rhs


public export
Extender : {n : Nat} -> Extender (FreeAbelianGroupOver n)
Extender other = MkHomomorphism
  { H = FreeExtenderHomomorphism other
  , preserves = extenderIsMorphism other
  }

public export
uniqueExtender : {n : Nat} -> (other : AbelianGroupTheory `ModelOver` (cast $ Fin n)) ->
   (extend : FreeAbelianGroupOver n ~> other) -> (xs : U (Model n)) ->
   other.Model.rel (extend.H.H.H xs)
                   (FreeExtenderFunction other xs)

public export
Uniqueness : {n : Nat} -> Uniqueness (FreeAbelianGroupOver n)
Uniqueness other extend1 extend2 xs =
  CalcWith (cast other.Model) $
  |~ extend1.H.H.H xs
  ~~ FreeExtenderFunction other xs ...(uniqueExtender other extend1 xs)
  ~~ extend2.H.H.H xs              ..<(uniqueExtender other extend2 xs)

public export
Free : {n : Nat} -> Free AbelianGroupTheory (cast $ Fin n)
Free = MkFree
  { Data = FreeAbelianGroupOver n
  , UP   = IsFree
    { Exists = Extender
    , Unique = Uniqueness
    }
  }