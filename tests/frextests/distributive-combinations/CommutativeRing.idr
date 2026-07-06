||| Test for the distributive combination of commutative monoids over abelian groups
module CommutativeRing

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Group.Abelian
import Frexlet.Group.Abelian.Notation.Core

import Data.Order

%default total

------------------------ DEFINING THE COMBINATION ------------------------

CommutativeRing : (n : Nat) -> (DistributiveCombinationTheory AbelianGroupTheory CommutativeMonoidTheory) `ModelOver` (cast $ Fin n)
CommutativeRing n =
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
    {additive = Theory.AbelianGroupTheory} 
    {multiplicative = Theory.CommutativeMonoidTheory} 
    (cast $ Fin n) freeM (Free x_set)


TestRing : (DistributiveCombinationTheory AbelianGroupTheory CommutativeMonoidTheory) `ModelOver` (cast $ Fin 3)
TestRing = CommutativeRing 3

X0, X1, X2 : U TestRing .Model
X0 = TestRing .Env.H 0
X1 = TestRing .Env.H 1
X2 = TestRing .Env.H 2

(.+.) : U TestRing .Model -> U TestRing .Model -> U TestRing .Model
(.+.) = TestRing .Model.sem (Left (Mono Product))

(.*.) : U TestRing .Model -> U TestRing .Model -> U TestRing .Model
(.*.) = TestRing .Model.sem (Right Product)

inv : U TestRing .Model -> U TestRing .Model
inv = TestRing .Model.sem (Left Inverse)

O1 : U TestRing .Model
O1 = TestRing .Model.sem (Left (Mono Neutral))

I1 : U TestRing .Model
I1 = TestRing .Model.sem (Right Neutral)

0 (=-=) : U TestRing .Model -> U TestRing .Model -> Type
(=-=) term1 term2 = TestRing .Model.rel term1 term2

refl : (x : U TestRing .Model) -> x =-= x
refl x = TestRing .Model.equivalence.reflexive x

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

invProductLeft : (inv X0) .*. X1 =-= inv (X0 .*. X1)
invProductLeft = refl (inv (X0 .*. X1))

invProductRight : X0 .*. (inv X1) =-= inv (X0 .*. X1)
invProductRight = refl (inv (X0 .*. X1))