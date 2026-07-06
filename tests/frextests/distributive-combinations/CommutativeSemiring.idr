||| Test for the distributive combination of monoids over commutative monoids
module CommutativeSemiring

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Commutative.Notation.Core

import Data.Order

------------------------ DEFINING THE COMBINATION ------------------------

CommutativeSemiringOver : (n : Nat) -> (DistributiveCombinationTheory CommutativeMonoidTheory CommutativeMonoidTheory) `ModelOver` (cast $ Fin n)
CommutativeSemiringOver n =
  let freeM : Free CommutativeMonoidTheory (cast $ Fin n)
      freeM = Finite.Free
      x_set : OrdSetoid
      x_set = MkOrdSetoid
        { setoid = cast freeM.Data.Model
        , decOrd = MkStrictOrd
          { lt = LtVect LT
          , ltDec = believe_me "ltDec"
          , ltIsOrder = believe_me "ltIsOrder"
          , compare = compareVect compareNat
          }
        }
  in
  DistributiveCombination' 
    {additive = Theory.CommutativeMonoidTheory} 
    {multiplicative = Theory.CommutativeMonoidTheory} 
    (cast $ Fin n) freeM (Free x_set)

TestSemiring : (DistributiveCombinationTheory CommutativeMonoidTheory CommutativeMonoidTheory) `ModelOver` (cast $ Fin 3)
TestSemiring = CommutativeSemiringOver 3

X0, X1, X2 : U TestSemiring .Model
X0 = TestSemiring .Env.H 0
X1 = TestSemiring .Env.H 1
X2 = TestSemiring .Env.H 2

(.+.) : U TestSemiring .Model -> U TestSemiring .Model -> U TestSemiring .Model
(.+.) = TestSemiring .Model.sem (Left Product)

(.*.) : U TestSemiring .Model -> U TestSemiring .Model -> U TestSemiring .Model
(.*.) = TestSemiring .Model.sem (Right Product)

O1 : U TestSemiring .Model
O1 = TestSemiring .Model.sem (Left Neutral)

I1 : U TestSemiring .Model
I1 = TestSemiring .Model.sem (Right Neutral)

0 (=-=) : U TestSemiring .Model -> U TestSemiring .Model -> Type
(=-=) term1 term2 = TestSemiring .Model.rel term1 term2

refl : (x : U TestSemiring .Model) -> x =-= x
refl x = TestSemiring .Model.equivalence.reflexive x

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

mulComm : (X0 .*. X1) =-= (X1 .*. X0)
mulComm = refl (X0 .*. X1)

mulLftNeutrality : (I1 .*. X0) =-= X0
mulLftNeutrality = refl (I1 .*. X0)

mulRgtNeutrality : (X0 .*. I1) =-= X0
mulRgtNeutrality = refl (X0 .*. I1)

distrLeft : (X0 .*. (X1 .+. X2)) =-= ((X0 .*. X1) .+. (X0 .*. X2))
distrLeft = refl (X0 .*. (X1 .+. X2))

distrRight : ((X0 .+. X1) .*. X2) =-= ((X0 .*. X2) .+. (X1 .*. X2))
distrRight = refl ((X0 .+. X1) .*. X2)

lftAnnihilation : (O1 .*. X0) =-= O1
lftAnnihilation = refl (O1 .*. X0)

rgtAnnihilation : (X0 .*. O1) =-= O1
rgtAnnihilation = refl (X0 .*. O1)