module Semrng

import Frex
import Frexlet.Semigroup
import Frexlet.Semigroup.Commutative

||| The sem-rng structure over the set of n variables
SemrngStructureOver : (n : Nat) -> SetoidAlgebra 
  (CoproductSignature Semigroup.Theory.Signature Semigroup.Commutative.Theory.Signature)
SemrngStructureOver n = DistributiveCombinationStructure' (cast $ Fin n) ?freeM ?freeA