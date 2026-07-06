||| Test for the distributive combination of semigroups over commutative semigroups
module Semrng

import Frex
import Frexlet.Semigroup
import Frexlet.Semigroup.Commutative
import Frexlet.Semigroup.Commutative.Notation.Core

import Frexlet.Semigroup.Frex.Order

import Data.List1

%default total

------------------------ DEFINING THE COMBINATION ------------------------

SemrngOver : (n : Nat) -> (DistributiveCombinationTheory CommutativeSemigroupTheory SemigroupTheory) `ModelOver` (cast $ Fin n)
SemrngOver n =
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
    {additive = Theory.CommutativeSemigroupTheory} 
    {multiplicative = Theory.SemigroupTheory} 
    (cast $ Fin n) freeM (Free x_set)

TestSemrng : (DistributiveCombinationTheory CommutativeSemigroupTheory SemigroupTheory) `ModelOver` (cast $ Fin 3)
TestSemrng = SemrngOver 3

X0, X1, X2 : U TestSemrng .Model
X0 = TestSemrng .Env.H 0
X1 = TestSemrng .Env.H 1
X2 = TestSemrng .Env.H 2

(.+.) : U TestSemrng .Model -> U TestSemrng .Model -> U TestSemrng .Model
(.+.) = TestSemrng .Model.sem (Left Product)

(.*.) : U TestSemrng .Model -> U TestSemrng .Model -> U TestSemrng .Model
(.*.) = TestSemrng .Model.sem (Right Product)

0 (=-=) : U TestSemrng .Model -> U TestSemrng .Model -> Type
(=-=) term1 term2 = TestSemrng .Model.rel term1 term2

refl : (x : U TestSemrng .Model) -> x =-= x
refl x = TestSemrng .Model.equivalence.reflexive x

------------------------ TESTING ------------------------


addAssoc : X0 .+. (X1 .+. X2) =-= (X0 .+. X1) .+. X2
addAssoc = refl (X0 .+. (X1 .+. X2))

addComm : (X0 .+. X1) =-= (X1 .+. X0)
addComm = refl (X0 .+. X1)

mulAssoc : (X0 .*. (X1 .*. X2)) =-= ((X0 .*. X1) .*. X2)
mulAssoc = refl (X0 .*. (X1 .*. X2))

distrLeft : (X0 .*. (X1 .+. X2)) =-= ((X0 .*. X1) .+. (X0 .*. X2))
distrLeft = refl (X0 .*. (X1 .+. X2))

distrRight : ((X0 .+. X1) .*. X2) =-= ((X0 .*. X2) .+. (X1 .*. X2))
distrRight = refl ((X0 .+. X1) .*. X2)