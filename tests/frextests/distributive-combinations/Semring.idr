||| Test for the distributive combination of monoids over commutative monoids
module Semring

import Frex
import Frexlet.Monoid
import Frexlet.Semigroup.Commutative
import Frexlet.Semigroup.Commutative.Notation.Core

import Frexlet.Monoid.Frex.Order

%default total
%hide Notation.Multiplicative.infixl.(.*.)

------------------------ DEFINING THE COMBINATION ------------------------

SemringOver : (n : Nat) -> (DistributiveCombinationTheory CommutativeSemigroupTheory MonoidTheory) `ModelOver` (cast $ Fin n)
SemringOver n =
  let freeM : Free Theory.MonoidTheory (cast $ Fin n)
      freeM = Monoid.Free.FreeMonoidOver $ cast $ Fin n
      x_set : OrdSetoid
      x_set = MkOrdSetoid
        { setoid = cast freeM.Data.Model
        , decOrd = MkStrictOrd
          { lt = LtUltList LtFin LtUnit
          , ltDec = believe_me "ltDec"
          , ltIsOrder = believe_me "ltIsOrder"
          , compare = compareUltList compareFin compareUnit
          }
        }
  in
  DistributiveCombination' 
    {additive = Theory.CommutativeSemigroupTheory} 
    {multiplicative = Theory.MonoidTheory} 
    (cast $ Fin n) freeM (Free x_set)

TestSemring : (DistributiveCombinationTheory CommutativeSemigroupTheory MonoidTheory) `ModelOver` (cast $ Fin 3)
TestSemring = SemringOver 3

X0, X1, X2 : U TestSemring .Model
X0 = TestSemring .Env.H 0
X1 = TestSemring .Env.H 1
X2 = TestSemring .Env.H 2

(.+.) : U TestSemring .Model -> U TestSemring .Model -> U TestSemring .Model
(.+.) = TestSemring .Model.sem (Left Product)

(.*.) : U TestSemring .Model -> U TestSemring .Model -> U TestSemring .Model
(.*.) = TestSemring .Model.sem (Right Product)

I1 : U TestSemring .Model
I1 = TestSemring .Model.sem (Right Neutral)

0 (=-=) : U TestSemring .Model -> U TestSemring .Model -> Type
(=-=) term1 term2 = TestSemring .Model.rel term1 term2

refl : (x : U TestSemring .Model) -> x =-= x
refl x = TestSemring .Model.equivalence.reflexive x

------------------------ TESTING ------------------------

addAssoc : X0 .+. (X1 .+. X2) =-= (X0 .+. X1) .+. X2
addAssoc = refl (X0 .+. (X1 .+. X2))

addComm : (X0 .+. X1) =-= (X1 .+. X0)
addComm = refl (X0 .+. X1)

mulAssoc : (X0 .*. (X1 .*. X2)) =-= ((X0 .*. X1) .*. X2)
mulAssoc = refl (X0 .*. (X1 .*. X2))

mulLftNeutrality : (I1 .*. X0) =-= X0
mulLftNeutrality = refl (I1 .*. X0)

mulRgtNeutrality : (X0 .*. I1) =-= X0
mulRgtNeutrality = refl (X0 .*. I1)

distrLeft : (X0 .*. (X1 .+. X2)) =-= ((X0 .*. X1) .+. (X0 .*. X2))
distrLeft = refl (X0 .*. (X1 .+. X2))

distrRight : ((X0 .+. X1) .*. X2) =-= ((X0 .*. X2) .+. (X1 .*. X2))
distrRight = refl ((X0 .+. X1) .*. X2)