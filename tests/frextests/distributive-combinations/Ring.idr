||| Test for the distributive combination of monoids over abelian groups
module Ring

import Frex
import Frexlet.Monoid
import Frexlet.Group.Abelian
import Frexlet.Group.Abelian.Notation.Core

import Frexlet.Monoid.Frex.Order

%default total

------------------------ DEFINING THE COMBINATION ------------------------

RingOver : (n : Nat) -> (DistributiveCombinationTheory AbelianGroupTheory MonoidTheory) `ModelOver` (cast $ Fin n)
RingOver n =
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
    {additive = Theory.AbelianGroupTheory} 
    {multiplicative = Theory.MonoidTheory} 
    (cast $ Fin n) freeM (Free x_set)

TestRing : (DistributiveCombinationTheory AbelianGroupTheory MonoidTheory) `ModelOver` (cast $ Fin 3)
TestRing = RingOver 3

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

