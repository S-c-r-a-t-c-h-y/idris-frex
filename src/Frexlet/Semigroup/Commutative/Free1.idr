||| This was the first attempt at implementing the free commutative semigroup
||| over the set of n variables.

module Frexlet.Semigroup.Commutative.Free1

import Frex

import Frexlet.Semigroup.Commutative.Theory
import Frexlet.Semigroup.Commutative.Dirac
import Frexlet.Semigroup.Commutative.Notation.Core

import Data.Vect
import Data.Vect.Quantifiers
import Data.Maybe

import Data.Setoid
import Data.Setoid.Vect
import Data.Setoid.Pair

import Decidable.Equality

%default total

public export
record FreeCarrier (n : Nat) where
  constructor MkFreeCarrier
  coeffs : Vect n Nat
  nonEmpty : Any (LTE 1) coeffs

public export
natSetoid : Setoid
natSetoid = cast Nat

h1 : (x : FreeCarrier n) -> (y : FreeCarrier n) -> ((i : Fin n) -> index i (x .coeffs) = index i (y .coeffs)) -> (i : Fin n) -> index i (y .coeffs) = index i (x .coeffs)
h1 x y prf i = natSetoid.equivalence.symmetric (index i (x .coeffs)) (index i (y .coeffs)) (prf i)

-- TODO: fix
public export
FreeSetoid : (n : Nat) -> Setoid
FreeSetoid n = MkSetoid
  { U           = FreeCarrier n
  , equivalence = MkEquivalence
    { relation    = \xs,ys                     => natSetoid.VectEquality xs.coeffs ys.coeffs
    , reflexive   = \xs, i                     => natSetoid.equivalence.reflexive _
    , symmetric   = h1
    --  \xs, ys, prf, j            => natSetoid.equivalence.symmetric (index j (xs .coeffs)) (index j (ys .coeffs)) (prf j)
    , transitive  = \xs, ys, zs, prf1, prf2, i => natSetoid.equivalence.transitive _ _ _ ?p2 ?p3
    }
  }

public export
zipWithNonEmpty : (xs, ys : Vect n Nat) -> 
  (prf : Any (LTE 1) xs) -> 
  Any (LTE 1) (zipWith (+) xs ys)
zipWithNonEmpty (x :: xs) (y :: ys) (Here prf) = Here $ plusLteMonotone prf LTEZero
zipWithNonEmpty (x :: xs) (y :: ys) (There prf) = There $ zipWithNonEmpty xs ys prf
  
public export
Add : {n : Nat} -> FreeCarrier n -> FreeCarrier n -> FreeCarrier n
Add xs ys = MkFreeCarrier
  { coeffs   = zipWith (+) xs.coeffs ys.coeffs
  , nonEmpty = zipWithNonEmpty xs.coeffs ys.coeffs xs.nonEmpty
  }

public export
AddHomomorphism : {n : Nat} ->
  SetoidHomomorphism (FreeSetoid n `Pair` FreeSetoid n) (FreeSetoid n) (Prelude.uncurry Add)
AddHomomorphism (xs1, ys1) (xs2, ys2) (MkAnd xs1_eq_xs2 ys1_eq_ys2) i = 
  CalcWith natSetoid $
  |~ index i (Add xs1 ys1).coeffs
  ~~ index i xs1.coeffs + index i ys1.coeffs ... (zipWithIndexLinear _ _ _ i)
  ~~ index i xs1.coeffs + index i ys2.coeffs ... (cong (index i xs1.coeffs +) (ys1_eq_ys2 i))
  ~~ index i xs2.coeffs + index i ys2.coeffs ... (cong (+ index i ys2.coeffs) (xs1_eq_xs2 i))
  ~~ index i (Add xs2 ys2).coeffs            ..< (zipWithIndexLinear _ _ _ i)

public export
FreeCommutativeSemigroupStructureOver : (n : Nat) -> CommutativeSemigroupStructure
FreeCommutativeSemigroupStructureOver n = MkSetoidAlgebra
  { algebra = MkAlgebra (FreeCarrier n) $ \Product => Add
  , equivalence = (FreeSetoid n).equivalence
  , congruence = \case
      MkOp Product => \ [xs1,ys1],[xs2,ys2],prf => 
          AddHomomorphism (xs1,ys1) (xs2,ys2) (MkAnd (prf 0) (prf 1))
  }

public export
AddAssociative : {n : Nat} -> (xs, ys, zs : FreeCarrier n) ->
  (FreeSetoid n).equivalence.relation
    (Add xs (Add ys zs))
    (Add (Add xs ys) zs)
AddAssociative xs ys zs i = CalcWith natSetoid $
  |~ index i (Add xs (Add ys zs)).coeffs 
  ~~ index i xs.coeffs + index i (Add ys zs).coeffs 
            ... (zipWithIndexLinear _ _ _ i)
  ~~ index i xs.coeffs + (index i ys.coeffs + index i zs.coeffs) 
            ... (cong (index i xs.coeffs +) $ zipWithIndexLinear _ _ _ i)
  ~~ (index i xs.coeffs + index i ys.coeffs) + index i zs.coeffs 
            ... (plusAssociative _ _ _)
  ~~ (index i (Add xs ys).coeffs) + index i zs.coeffs   
            ..< (cong (+ index i zs.coeffs) $ zipWithIndexLinear _ _ _ i)
  ~~ index i (Add (Add xs ys) zs).coeffs
            ..< (zipWithIndexLinear _ _ _ i)
    

public export
AddCommutative : {n : Nat} -> (xs, ys : FreeCarrier n) ->
  (FreeSetoid n).equivalence.relation
    (Add xs ys)
    (Add ys xs)
AddCommutative xs ys i = CalcWith natSetoid $
  |~ index i (Add xs ys).coeffs
  ~~ index i xs.coeffs + index i ys.coeffs ... (zipWithIndexLinear _ _ _ i)
  ~~ index i ys.coeffs + index i xs.coeffs ... (plusCommutative _ _)
  ~~ index i (Add ys xs).coeffs            ..< (zipWithIndexLinear _ _ _ i)
    

public export
FreeValidatesAxioms : (n : Nat) -> 
  Validates CommutativeSemigroupTheory (FreeCommutativeSemigroupStructureOver n)
FreeValidatesAxioms n (Sem Associativity) env = AddAssociative (env 0) (env 1) (env 2)
FreeValidatesAxioms n Commutativity env = AddCommutative (env 0) (env 1)


public export
Model : (n : Nat) -> CommutativeSemigroup
Model n = MkModel
  { Algebra = FreeCommutativeSemigroupStructureOver n
  , Validate = FreeValidatesAxioms n
  }


public export
unitCoeffs : (n : Nat) -> Fin n -> Vect n Nat
unitCoeffs n i = Fin.tabulate $ dirac i

public export
tabulateAny : (f : Fin n -> x) -> (i : Fin n) ->
  (prop : p (f i)) -> Any p (Fin.tabulate f)
tabulateAny f FZ prop = Here prop
tabulateAny f (FS y) prop = There (tabulateAny (\x => f (FS x)) y prop)


public export
unitCoeffsNonEmpty : (n : Nat) -> (i : Fin n) ->
  Any (LTE 1) (unitCoeffs n i)  
unitCoeffsNonEmpty n i = tabulateAny (dirac i) i $ 
  rewrite diracOnDiagonal i in LTESucc LTEZero


public export
unit : (n : Nat) -> Fin n -> FreeCarrier n
unit n i = MkFreeCarrier
  { coeffs = unitCoeffs n i
  , nonEmpty = unitCoeffsNonEmpty n i
  }

public export
FreeCommutativeSemigroupOver : (n : Nat) -> CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)
FreeCommutativeSemigroupOver n = MkModelOver
  { Model = Model n
  , Env = mate $ unit n
  }

----------------------------------------------- FREENESS PROOF ----------------------------------------------

-- support : FreeCarrier n -> List1 (Fin n, Nat)
-- support [] = []
-- support (x :: xs) = ?support_rhs_1

public export
coeffEval : (other : CommutativeSemigroup) ->
  Nat -> U other -> Maybe $ U other
coeffEval other 0     _ = Nothing
coeffEval other (S k) x = Just $ other.mult (S k) x

public export
coeffEvalIsJust : (other : CommutativeSemigroup) ->
  (n : Nat) -> {auto nz : Positive n} -> (x : U other) ->
  IsJust (coeffEval other n x) 
coeffEvalIsJust other 0 {nz} x = absurd $ uninhabited nz
coeffEvalIsJust other (S k) x = ItIsJust

public export
combine : (other : CommutativeSemigroup) ->
  Maybe (U other) -> Maybe (U other) -> Maybe (U other)
combine other Nothing     y     = y
combine other (Just x) Nothing  = Just x
combine other (Just x) (Just y) = Just $ other.sem Product x y

public export
combineNothingLeft : (other : CommutativeSemigroup) ->
  (x : Maybe (U other)) ->
  combine other Nothing x = x
combineNothingLeft other Nothing = Refl
combineNothingLeft other (Just x) = Refl

public export
combineNothingRight : (other : CommutativeSemigroup) ->
  (x : Maybe (U other)) ->
  combine other x Nothing = x
combineNothingRight other Nothing = Refl
combineNothingRight other (Just x) = Refl

public export
isJustCombineLeft : (other : CommutativeSemigroup) ->
  (x, y : Maybe (U other)) -> (IsJust x) ->
  IsJust (combine other x y)
isJustCombineLeft other (Just x) Nothing  _ = ItIsJust
isJustCombineLeft other (Just x) (Just y) _ = ItIsJust

public export
isJustCombineRight : (other : CommutativeSemigroup) ->
  (x, y : Maybe (U other)) -> (IsJust y) ->
  IsJust (combine other x y)
isJustCombineRight other Nothing (Just y)  _ = ItIsJust
isJustCombineRight other (Just x) (Just y) _ = ItIsJust

public export
extMaybe : {n : Nat} -> (other : CommutativeSemigroup) ->
  (Fin n -> U other) ->
  Vect n Nat -> Maybe $ U other
extMaybe other env [] = Nothing
extMaybe other env (x :: xs) = 
  combine other (coeffEval other x (env FZ))
                (extMaybe other (env . FS) xs)
  
%hint
public export
extMaybeNonEmpty : {n : Nat} -> (other : CommutativeSemigroup) ->
  (env : Fin n -> U other) -> (xs : Vect n Nat) -> (nonEmpty : Any (LTE 1) xs) ->
  IsJust (extMaybe other env xs)
extMaybeNonEmpty other env (0 :: xs) (There prf) = 
  extMaybeNonEmpty other (env . FS) xs prf
extMaybeNonEmpty other env ((S k) :: xs) nonEmpty = 
  isJustCombineLeft other _ _ ItIsJust

public export
FreeExtenderFunction : {n : Nat} -> ExtenderFunction (FreeCommutativeSemigroupOver n)
FreeExtenderFunction other x = 
  fromJust (extMaybe other.Model other.Env.H x.coeffs)
  @{extMaybeNonEmpty other.Model other.Env.H x.coeffs x.nonEmpty}

-- extMaybePlus : (other : CommutativeSemigroup) ->
--     (xs, ys : Vect n Nat) -> (env : Fin n -> U other) ->
--     other.rel  (extMaybe other env (zipWith (+) xs ys))
--                (combine other (extMaybe other env xs) (extMaybe other env ys))

public export
congFromJust : (x, y : Maybe a) -> 
  IsJust x -> IsJust y -> (x = y) -> 
  fromJust x = fromJust y 
congFromJust (Just x) (Just y) _ _ prf = injective prf


public export
FreeExtenderSetoidHomomorphism : {n : Nat} -> ExtenderSetoidHomomorphism (FreeCommutativeSemigroupOver n)
FreeExtenderSetoidHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderFunction other
  , homomorphic = \xs,ys,prf => Data.Setoid.Definition.reflect (cast other.Model)
                              $ congFromJust _ _ 
                                (extMaybeNonEmpty _ _ _ xs.nonEmpty) 
                                (extMaybeNonEmpty _ _ _ ys.nonEmpty)
                              $ cong (extMaybe other.Model other.Env.H)
                              $ vectorExtensionality xs.coeffs ys.coeffs prf
  }

-- fromJustCombinePlus : (other : CommutativeSemigroup) ->
--   (env : Fin n -> U other) -> (xs, ys : Vect n Nat) ->
--   (xs_ne : Any (LTE 1) xs) -> (ys_ne : Any (LTE 1) ys) ->
--   (prf1 : IsJust $ extMaybe other env (zipWith (+) xs ys)) ->
--   (prf2 : IsJust $ combine other (extMaybe other env xs) (extMaybe other env ys)) ->
--   other.rel (fromJust (extMaybe other env (zipWith (+) xs ys)))
--             (fromJust (combine other (extMaybe other env xs) (extMaybe other env ys)))
-- fromJustCombinePlus other env (0 :: xs) (0 :: ys) (There prf1) (There prf2) p1 _ = 
--   rewrite combineNothingLeft other (extMaybe other (env . FS) (zipWith (+) xs ys)) in
--   rewrite combineNothingLeft other (extMaybe other (env . FS) xs) in
--   rewrite combineNothingLeft other (extMaybe other (env . FS) ys) in
--   fromJustCombinePlus other (env . FS) xs ys prf1 prf2 
--   (extMaybeNonEmpty other (env . FS) (zipWith (+) xs ys) $ zipWithNonEmpty xs ys prf1)
--   (isJustCombineLeft other _ _ $ extMaybeNonEmpty other (env . FS) xs prf1)
-- fromJustCombinePlus other env (0 :: xs) ((S j) :: ys) xs_ne ys_ne _ _ = ?fromJustCombinePlus_rhs_6
-- fromJustCombinePlus other env ((S k) :: xs) (0 :: ys) xs_ne ys_ne _ _ = ?fromJustCombinePlus_rhs_7
-- fromJustCombinePlus other env ((S k) :: xs) ((S j) :: ys) xs_ne ys_ne _ _ = ?fromJustCombinePlus_rhs_8

public export
extenderPreservesPlus : {n : Nat} -> (other : CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)) ->
  Preserves (Model n).Algebra other.Model.Algebra (FreeExtenderFunction other) Plus
extenderPreservesPlus other [(MkFreeCarrier [] ne), _] = absurd $ uninhabited ne
extenderPreservesPlus other [(MkFreeCarrier (0 :: xs) ne1), (MkFreeCarrier (0 :: ys) ne2)] = ?rhs2_8
extenderPreservesPlus other [(MkFreeCarrier (0 :: xs) ne1), (MkFreeCarrier ((S j) :: ys) ne2)] = ?rhs2_9
extenderPreservesPlus other [(MkFreeCarrier ((S k) :: xs) ne1), (MkFreeCarrier (0 :: ys) ne2)] = ?rhs2_10
extenderPreservesPlus other [(MkFreeCarrier ((S k) :: xs) ne1), (MkFreeCarrier ((S j) :: ys) ne2)] = ?rhs2_11

public export
FreeExtenderHomomorphism : {n : Nat} -> ExtenderAlgebraHomomorphism (FreeCommutativeSemigroupOver n)
FreeExtenderHomomorphism other = MkSetoidHomomorphism
  { H = FreeExtenderSetoidHomomorphism other
  , preserves = \case
      MkOp Product => extenderPreservesPlus other
  }

public export
extMaybeEmpty : {n : Nat} -> (other : CommutativeSemigroup) ->
  (env : Fin n -> U other) ->
  extMaybe other env (Fin.tabulate (\x => 0)) = Nothing
extMaybeEmpty {n = 0} other env = Refl
extMaybeEmpty {n = (S k)} other env = extMaybeEmpty other (env . FS)

extenderIsMorphism' : {n : Nat} -> (other : CommutativeSemigroup) ->
  (env : Fin n -> U other) -> (x : Fin n) ->
  other.rel (fromJust (extMaybe other env (unitCoeffs n x))
              @{extMaybeNonEmpty other env (unitCoeffs n x) (unitCoeffsNonEmpty n x)})
            (env x)
-- extenderIsMorphism' other env FZ =
--   rewrite extMaybeEmpty other (env . FS) in
--   Data.Setoid.Definition.reflect (cast other) Refl
-- extenderIsMorphism' {n = S k} other env (FS i) = 
--   -- CalcWith (cast other) $
--   -- |~ fromJust (extMaybe other env (unitCoeffs (S k) (FS i)))
--   --      @{extMaybeNonEmpty other env (unitCoeffs (S k) (FS i)) (unitCoeffsNonEmpty (S k) (FS i))}
--   -- ~~ fromJust (extMaybe other (env . FS) (unitCoeffs k i))
--   --      @{extMaybeNonEmpty other (env . FS) (unitCoeffs k i) (unitCoeffsNonEmpty k i)} .=. (?prf1)
--   -- ~~ ?eq1 ... (?prf2)
--   extenderIsMorphism' {n = k} other (env . FS) i

public export
extenderIsMorphism : {n : Nat} -> (other : CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)) ->
  PreservesEnv (FreeCommutativeSemigroupOver n) other (FreeExtenderSetoidHomomorphism other)
extenderIsMorphism other x = extenderIsMorphism' other.Model other.Env.H x


public export
Extender : {n : Nat} -> Extender (FreeCommutativeSemigroupOver n)
Extender other = MkHomomorphism
  { H = FreeExtenderHomomorphism other
  , preserves = extenderIsMorphism other
  }

public export
uniqueExtender : {n : Nat} -> (other : CommutativeSemigroupTheory `ModelOver` (cast $ Fin n)) ->
   (extend : FreeCommutativeSemigroupOver n ~> other) -> (xs : U (Model n)) ->
   other.Model.rel (extend.H.H.H xs)
                   (FreeExtenderFunction other xs)

public export
Uniqueness : {n : Nat} -> Uniqueness (FreeCommutativeSemigroupOver n)
Uniqueness other extend1 extend2 xs =
  CalcWith (cast other.Model) $
  |~ extend1.H.H.H xs
  ~~ FreeExtenderFunction other xs ...(uniqueExtender other extend1 xs)
  ~~ extend2.H.H.H xs              ..<(uniqueExtender other extend2 xs)

public export
Free : {n : Nat} -> Free CommutativeSemigroupTheory (cast $ Fin n)
Free = MkFree
  { Data = FreeCommutativeSemigroupOver n
  , UP   = IsFree
    { Exists = Extender
    , Unique = Uniqueness
    }
  }
