||| Test for the distributive combination of semigroups over abelian groups
module Rng

import Frex
import Frexlet.Semigroup
import Frexlet.Group.Abelian
import Frexlet.Group.Abelian.Notation.Core

import Frexlet.Semigroup.Frex.Order

import Data.List1

%default total

------------------------ DEFINING THE COMBINATION ------------------------

RngOver : (n : Nat) -> (DistributiveCombinationTheory AbelianGroupTheory SemigroupTheory) `ModelOver` (cast $ Fin n)
RngOver n =
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
    {additive = Theory.AbelianGroupTheory} 
    {multiplicative = Theory.SemigroupTheory} 
    (cast $ Fin n) freeM (Free x_set)

TestRng : (DistributiveCombinationTheory AbelianGroupTheory SemigroupTheory) `ModelOver` (cast $ Fin 3)
TestRng = RngOver 3

X0, X1, X2 : U TestRng .Model
X0 = TestRng .Env.H 0
X1 = TestRng .Env.H 1
X2 = TestRng .Env.H 2

(.+.) : U TestRng .Model -> U TestRng .Model -> U TestRng .Model
(.+.) = TestRng .Model.sem (Left (Mono Product))

(.*.) : U TestRng .Model -> U TestRng .Model -> U TestRng .Model
(.*.) = TestRng .Model.sem (Right Product)

inv : U TestRng .Model -> U TestRng .Model
inv = TestRng .Model.sem (Left Inverse)

O1 : U TestRng .Model
O1 = TestRng .Model.sem (Left (Mono Neutral))

0 (=-=) : U TestRng .Model -> U TestRng .Model -> Type
(=-=) term1 term2 = TestRng .Model.rel term1 term2

refl : (x : U TestRng .Model) -> x =-= x
refl x = TestRng .Model.equivalence.reflexive x

------------------------ TESTING ------------------------

addAssoc : X0 .+. (X1 .+. X2) =-= (X0 .+. X1) .+. X2
addAssoc = refl (X0 .+. (X1 .+. X2))

addComm : (X0 .+. X1) =-= (X1 .+. X0)
addComm = refl (X0 .+. X1)

addLftNeutrality : (O1 .+. X0) =-= X0
addLftNeutrality = refl (O1 .+. X0)

addRgtNeutrality : (X0 .+. O1) =-= X0
addRgtNeutrality = refl (X0 .+. O1)

addLftInverse : (inv X0 .+. X0) =-= O1
addLftInverse = refl (inv X0 .+. X0)

addRgtInverse : (X0 .+. inv X0) =-= O1
addRgtInverse = refl (X0 .+. inv X0)

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