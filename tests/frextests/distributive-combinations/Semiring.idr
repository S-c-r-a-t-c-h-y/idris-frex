module Semiring

import Frex
import Frexlet.Monoid
import Frexlet.Monoid.Commutative

SemiringStructure : SetoidAlgebra 
  (CoproductSignature Monoid.Theory.Signature Monoid.Commutative.Theory.Signature)
-- SemiringStructure = DistributiveCombinationStructure x ()