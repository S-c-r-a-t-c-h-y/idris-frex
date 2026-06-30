module Frexlet.Ring.Combination

import Frex

import Frexlet.Ring.Theory
import Frexlet.Monoid.Theory
import Frexlet.Monoid.Commutative.Theory

RingTheoryBis : Presentation
RingTheoryBis = DistributiveCombinationTheory CommutativeMonoidTheory MonoidTheory

RingBis : Type
RingBis = Model RingTheoryBis

-- RingValidatesRingBis : (a : Ring) -> Validates RingTheoryBis (a.Algebra)

RingIsRingBis : (a : Ring) -> RingBis
RingIsRingBis a = ?prf
  -- MkModel
  -- { Algebra   = a.Algebra
  --   Validates = ?validates
  -- }
