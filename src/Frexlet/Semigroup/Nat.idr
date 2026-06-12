||| Semigroup structures over the Nats
module Frexlet.Semigroup.Nat

import Frex
import Frexlet.Semigroup.Theory

import public Data.Nat

%default total

||| Additive semigroup structure over the natural numbers
public export
Additive : Semigroup
Additive = MkModel
  { Algebra = cast {from = Algebra Signature} $
      MkAlgebra {U = Nat, Sem = \case Product => plus}
  , Validate = \case
      Associativity => \env => plusAssociative _ _ _
  }

||| Multiplicative semigroup structure over the natural numbers
public export
Multiplicative : Semigroup
Multiplicative = MkModel
  { Algebra = cast {from = Algebra Signature} $
      MkAlgebra {U = Nat, Sem = \case Product => mult}
  , Validate = \case
      Associativity => \env => multAssociative _ _ _
  }