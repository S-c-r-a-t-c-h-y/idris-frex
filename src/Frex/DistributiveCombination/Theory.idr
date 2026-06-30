module Frex.DistributiveCombination.Theory

import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model

import Data.Setoid

import Data.Vect
import Data.Vect.Quantifiers

%default total

-------------------------------- Theory --------------------------------

||| A signature for the coproduct of two signatures
public export
CoproductSignature : Signature -> Signature -> Signature
CoproductSignature sigA sigM =
  MkSignature (\n => Either (sigA.OpWithArity n) (sigM.OpWithArity n))

public export
injAddOp :
  {sigA, sigM : Signature} ->
  sigA.OpWithArity n ->
  (CoproductSignature sigA sigM).OpWithArity n
injAddOp = Left

public export
injMulOp :
  {sigA, sigM : Signature} ->
  sigM.OpWithArity n ->
  (CoproductSignature sigA sigM).OpWithArity n
injMulOp = Right

||| Signature homomorphism from the additive signature to the coproduct signature
%hint
public export
castOpAdditive : 
     (additive, multiplicative : Signature) 
  -> additive ~> (CoproductSignature additive multiplicative)
castOpAdditive additive multiplicative =
  OpTranslation injAddOp

||| Signature homomorphism from the multiplicative signature to the coproduct signature
%hint
public export
castOpMultiplicative :
     (additive, multiplicative : Signature) 
  -> multiplicative ~> (CoproductSignature additive multiplicative)
castOpMultiplicative additive multiplicative =
  OpTranslation injMulOp

||| Casts for terms of the additive signature to terms of the coproduct signature
public export
injAddTerm : 
     {additiveSig, multiplicativeSig : _}
  -> Term additiveSig x
  -> (Term (CoproductSignature additiveSig multiplicativeSig) x)
injAddTerm t = Signature.cast {castOp=castOpAdditive additiveSig multiplicativeSig} t


||| Casts for terms of the multiplicative signature to terms of the coproduct signature
public export
injMulTerm : 
     {additiveSig, multiplicativeSig : _}
  -> Term multiplicativeSig x
  -> (Term (CoproductSignature additiveSig multiplicativeSig) x)
injMulTerm t = Signature.cast {castOp=castOpMultiplicative additiveSig multiplicativeSig} t

public export
injAddEq :
      {additiveSig, multiplicativeSig : _}
    -> Equation additiveSig
    -> Equation (CoproductSignature additiveSig multiplicativeSig)
injAddEq eq = MkEq
  { support = eq.support
  , lhs = injAddTerm eq.lhs
  , rhs = injAddTerm eq.rhs
  }

public export
injMulEq :
      {additiveSig, multiplicativeSig : _}
    -> Equation multiplicativeSig
    -> Equation (CoproductSignature additiveSig multiplicativeSig)
injMulEq eq = MkEq
  { support = eq.support
  , lhs = injMulTerm eq.lhs
  , rhs = injMulTerm eq.rhs
  }

public export
data DistributivityAxiom : Signature -> Signature -> Type where
  DistAxiom :
       {addSig, mulSig : Signature}
    -> {m, n : Nat}
    -> (addOp : addSig.OpWithArity m)
    -> (mulOp : mulSig.OpWithArity n)
    -> (i : Fin n)
    -> DistributivityAxiom addSig mulSig

public export
data CombinationAxiom : (additive, multiplicative : Presentation) -> Type where
  AddAx : additive.Axiom -> CombinationAxiom additive multiplicative
  MulAx : multiplicative.Axiom -> CombinationAxiom additive multiplicative
  DistAx : DistributivityAxiom additive.signature multiplicative.signature
          -> CombinationAxiom additive multiplicative 

public export
leftFin : Fin n -> Fin (n + m)
leftFin {m} = weakenN m

public export
rightFin : {n : Nat} -> Fin m -> Fin (n + m)
rightFin = shift n

public export
addTerm :
     {addSig, mulSig : Signature}
  -> {m : Nat}
  -> addSig.OpWithArity m
  -> Vect m (Term (CoproductSignature addSig mulSig) vars)
  -> Term (CoproductSignature addSig mulSig) vars
addTerm f xs = Call (MkOp $ injAddOp f) xs

public export
mulTerm :
     {addSig, mulSig : Signature}
  -> {n : Nat}
  -> mulSig.OpWithArity n
  -> Vect n (Term (CoproductSignature addSig mulSig) vars)
  -> Term (CoproductSignature addSig mulSig) vars
mulTerm f xs = Call (MkOp $ injMulOp f) xs

public export
distributivityEquation :
     {addSig, mulSig : Signature}
  -> {m, n : Nat}
  -> (addOp : addSig.OpWithArity m)
  -> (mulOp : mulSig.OpWithArity n)
  -> (i : Fin n)
  -> Equation (CoproductSignature addSig mulSig)
distributivityEquation {m} {n} addOp mulOp i =
  MkEq (n + m) lhs rhs
  where
    xVars : Vect n (Term (CoproductSignature addSig mulSig) (Fin (n + m)))
    xVars = map (Done . leftFin {m = m}) (allFins n)

    yVars : Vect m (Term (CoproductSignature addSig mulSig) (Fin (n + m)))
    yVars = map (Done . rightFin {n = n}) (allFins m)

    lhsArgs : Vect n (Term (CoproductSignature addSig mulSig) (Fin (n + m)))
    lhsArgs = replaceAt i (addTerm addOp yVars) xVars

    lhs : Term (CoproductSignature addSig mulSig) (Fin (n + m))
    lhs = mulTerm mulOp lhsArgs

    rhsSummands : Vect m (Term (CoproductSignature addSig mulSig) (Fin (n + m)))
    rhsSummands = map (\y => mulTerm mulOp (replaceAt i y xVars)) yVars

    rhs : Term (CoproductSignature addSig mulSig) (Fin (n + m))
    rhs = addTerm addOp rhsSummands

public export
DistributiveCombinationTheory : Presentation -> Presentation -> Presentation
DistributiveCombinationTheory additive multiplicative =
  MkPresentation
    (CoproductSignature additive.signature multiplicative.signature)
    (CombinationAxiom additive multiplicative)
    (\case
       AddAx ax =>
         injAddEq (additive.axiom ax)
       MulAx ax =>
         injMulEq (multiplicative.axiom ax)
       DistAx (DistAxiom addOp mulOp i) =>
         distributivityEquation addOp mulOp i
    )

-------------------------------- COMMUTATIVE THEORY --------------------------------

||| pairFin i j is the index m * i + j. (i th row, j th column) in a matrix of size n * m
public export
pairFin : {n, m : Nat} -> Fin n -> Fin m -> Fin (n * m)
pairFin {n = S k} FZ j = weakenN (k * m) j
pairFin {n = S k} (FS i) j = shift m (pairFin {n = k} i j)

public export
commutationEquation :
  {m, n : Nat} ->
  {sig : Signature} ->
  (f : sig.OpWithArity m) ->
  (g : sig.OpWithArity n) ->
  Equation sig
commutationEquation f g = MkEq (n * m) lhs rhs
  where
    lhs : Term sig (Fin (n * m))
    lhs = Call (MkOp f) (map (\j => Call (MkOp g) (map (\i => Done (pairFin i j)) (allFins n))) (allFins m))

    rhs : Term sig (Fin (n * m))
    rhs = Call (MkOp g) (map (\i => Call (MkOp f) (map (\j => Done (pairFin i j)) (allFins m))) (allFins n))

public export 0
CommutativeTheory : Presentation -> Type
CommutativeTheory pres = 
  {m, n : Nat} -> 
  (f : pres.signature.OpWithArity m) ->
  (g : pres.signature.OpWithArity n) ->
  (M : Model pres) ->
  ValidatesEquation (commutationEquation f g) (Model.Algebra M)

-------------------------------- AFFINE THEORY --------------------------------

public export
sumUsages : {k, n : Nat} -> Vect k (Vect n Nat) -> Vect n Nat
sumUsages [] = replicate _ 0
sumUsages (u :: us) = zipWith (+) u (sumUsages us)

public export
usage : {n : Nat} -> Term sig (Fin n) -> Vect n Nat
usage (Done x) = Fin.tabulate (\i => if i == x then 1 else 0)
usage (Call f xs) = assert_total $ sumUsages (map usage xs) -- FIXME: maybe not use assert_total?

public export
AffineTerm : {n : Nat} -> Term sig (Fin n) -> Type
AffineTerm t = All (\k => LTE k 1) (usage t)

public export
lte1 : (n : Nat) -> {auto prf : lte n 1 === True} -> LTE n 1
lte1 n {prf} = lteReflectsLTE n 1 prf

public export
record AffineEquation (eq : Equation sig) where
  constructor MkAffineEq
  lhsAffine : AffineTerm eq.lhs
  rhsAffine : AffineTerm eq.rhs

public export
record AffinePresentation (pres : Presentation) where
  constructor MkAffinePresentation
  axiomsAffine : (ax : pres.Axiom) -> AffineEquation (pres.axiom ax)