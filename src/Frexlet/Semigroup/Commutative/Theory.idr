||| The syntax and axioms for semigroups
module Frexlet.Semigroup.Commutative.Theory

import Frex
import Frex.Algebra

import Syntax.PreorderReasoning
import Syntax.PreorderReasoning.Generic
-- import Syntax.PreorderReasoning.Setoid

import public Frexlet.Semigroup

%default total

private infixl 9 .*.

public export
data Axiom
  = Sem Semigroup.Theory.Axiom
  | Commutativity

public export
CommutativeSemigroupTheory : Presentation
CommutativeSemigroupTheory = MkPresentation Theory.Signature Commutative.Theory.Axiom $ \case
    Sem ax => (SemigroupTheory).axiom ax
    Commutativity => commutativity Product


public export
CommutativeSemigroup : Type
CommutativeSemigroup = Model CommutativeSemigroupTheory

public export
commutativity : (a : CommutativeSemigroup) -> (x, y, z, w : U a) ->
  let (.*.) = a.sem Product in
  a.rel
    ((x .*. z) .*. (y .*. w))
    ((x .*. y) .*. (z .*. w))
-- commutativity a x y z w = 
--   let (.*.) = a.sem Product in
--   CalcWith @{cast a} $
--   |~ ((x .*. z) .*. (y .*. w))
--   ~~ (x .*. (z .*. (y .*. w))) ... (a.validate (Sem Associativity) [_, _, _])
--   ~~ (x .*. ((z .*. y) .*. w)) ... (a.validate (Sem Associativity) [_, _, _])
--   ~~ (x .*. ((y .*. z) .*. w)) ... (a.validate (Commutativity) [_, _])
--   ~~ (x .*. (y .*. (z .*. w))) ... (a.validate (Sem Associativity) [_, _, _])
--   ~~ ((x .*. y) .*. (z .*. w)) ... (a.validate (Sem Associativity) [_, _, _])

public export
CommutativeSemigroupCommutative : commutativeTheory CommutativeSemigroupTheory
CommutativeSemigroupCommutative Product Product m env = 
  commutativity m (env 0) (env 1) (env 2) (env 3)

||| Smart constructor for commutative semigroups
public export
MkCommutativeSemigroup
  : (semigroup : Semigroup) ->
    (commutativity : ValidatesEquation
                       (Axiom.commutativity {sig = Theory.Signature} Product)
                       (semigroup.Algebra)) ->
    CommutativeSemigroup
MkCommutativeSemigroup semigroup commutativity = MkModel
  { Algebra = semigroup.Algebra
  , Validate = \case
      Sem ax        => semigroup.Validate ax
      Commutativity => commutativity
  }

public export
Cast CommutativeSemigroup Semigroup where
  cast csemigroup = MkModel
    { Algebra  = csemigroup.Algebra
    , Validate = \ax => csemigroup.Validate (Sem ax)
    }

public export
Plus : Op Signature
Plus = MkOp Product

export
[Raw] Show Commutative.Theory.Axiom where
  show = \case
    Sem ax => show @{Raw} ax
    Commutativity => "Commutativity"

export
[Words] Show Commutative.Theory.Axiom where
  show = \case
    Sem ax => show @{Words} ax
    Commutativity => "Commutativity"

export
Finite Commutative.Theory.Axiom where
  enumerate = map Sem enumerate ++ [Commutativity]

export
withRaw : Printer Signature a -> Printer CommutativeSemigroupTheory a
withRaw = MkPrinter "CommutativeSemigroupTheory" Raw

export
withWords : Printer Signature a -> Printer CommutativeSemigroupTheory a
withWords = MkPrinter "CommutativeSemigroupTheory" Words
