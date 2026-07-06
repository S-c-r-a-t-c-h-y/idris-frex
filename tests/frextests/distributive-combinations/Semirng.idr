||| Test for the distributive combination of semigroups over commutative monoids
module Semirng

import Frex
import Frexlet.Semigroup
import Frexlet.Monoid.Commutative

import Frexlet.Semigroup.Frex.Order

import Data.List1

------------------------ DEFINING THE COMBINATION ------------------------

SemirngOver : (n : Nat) -> (DistributiveCombinationTheory CommutativeMonoidTheory SemigroupTheory) `ModelOver` (cast $ Fin n)
SemirngOver n =
  let freeM : Free Theory.SemigroupTheory (cast $ Fin n)
      freeM = Semigroup.Free.FreeSemigroupOver $ cast $ Fin n
      x_set : OrdSetoid
      x_set = MkOrdSetoid
        { setoid = cast freeM.Data.Model
        , decOrd = MkStrictOrd
          { lt = LtMon
          , ltDec = believe_me "ltDec"
          , ltIsOrder = believe_me "ltIsOrder"
          , compare = compareMon
          }
        }
  in
  DistributiveCombination' 
    {additive = Theory.CommutativeMonoidTheory} 
    {multiplicative = Theory.SemigroupTheory} 
    (cast $ Fin n) freeM (Free x_set)

TestSemirng : (DistributiveCombinationTheory CommutativeMonoidTheory SemigroupTheory) `ModelOver` (cast $ Fin 3)
TestSemirng = SemirngOver 3

X0, X1, X2 : U TestSemirng .Model
X0 = TestSemirng .Env.H 0
X1 = TestSemirng .Env.H 1
X2 = TestSemirng .Env.H 2

(.+.) : U TestSemirng .Model -> U TestSemirng .Model -> U TestSemirng .Model
(.+.) = TestSemirng .Model.sem (Left Product)

(.*.) : U TestSemirng .Model -> U TestSemirng .Model -> U TestSemirng .Model
(.*.) = TestSemirng .Model.sem (Right Product)

O1 : U TestSemirng .Model
O1 = TestSemirng .Model.sem (Left Neutral)

0 (=-=) : U TestSemirng .Model -> U TestSemirng .Model -> Type
(=-=) term1 term2 = TestSemirng .Model.rel term1 term2

refl : (x : U TestSemirng .Model) -> x =-= x
refl x = TestSemirng .Model.equivalence.reflexive x

------------------------ TESTING ------------------------

addAssoc : X0 .+. (X1 .+. X2) =-= (X0 .+. X1) .+. X2
addAssoc = refl (X0 .+. (X1 .+. X2))

addComm : (X0 .+. X1) =-= (X1 .+. X0)
addComm = refl (X0 .+. X1)

addLftNeutrality : (O1 .+. X0) =-= X0
addLftNeutrality = refl (O1 .+. X0)

addRgtNeutrality : (X0 .+. O1) =-= X0
addRgtNeutrality = refl (X0 .+. O1)

mulAssoc : (X0 .*. (X1 .*. X2)) =-= ((X0 .*. X1) .*. X2)
mulAssoc = refl (X0 .*. (X1 .*. X2))

distrLeft : (X0 .*. (X1 .+. X2)) =-= ((X0 .*. X1) .+. (X0 .*. X2))
distrLeft = refl (X0 .*. (X1 .+. X2))

distrRight : ((X0 .+. X1) .*. X2) =-= ((X0 .*. X2) .+. (X1 .*. X2))
distrRight = refl ((X0 .+. X1) .*. X2)

lftAnnihilation : (O1 .*. X0) =-= O1
lftAnnihilation = refl (O1 .*. X0)

rgtAnnihilation : (X0 .*. O1) =-= O1
rgtAnnihilation = refl (X0 .*. O1)