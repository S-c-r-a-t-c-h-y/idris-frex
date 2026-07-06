module Frexlet.Monoid.InvolutiveSemiring

import Frex
import Frexlet.Monoid.Commutative
import Frexlet.Monoid.Involutive

import Frexlet.Monoid.Frex.Order


{-

NB: file temporarly put there so that the Idris LSP can typecheck definitions

-}


----------------------- DEFINING THE COMBINATION ------------------------

public export
InvSemiringOver : (n : Nat) -> (DistributiveCombinationTheory CommutativeMonoidTheory InvolutiveMonoidTheory) `ModelOver` (cast $ Fin n)
InvSemiringOver n =
  let freeM : Free Theory.InvolutiveMonoidTheory (cast $ Fin n)
      freeM = FreeInvolutiveMonoidOver n
      x_set : OrdSetoid
      x_set = MkOrdSetoid
        { setoid = cast freeM.Data.Model
        , decOrd = MkStrictOrd
          { lt = LtUltList (LexicographicLT LtBool LtFin) LtUnit
          , ltDec = believe_me "ltDec"
          , ltIsOrder = believe_me "ltIsOrder"
          , compare = compareUltList (compareLexicographic compareBool compareFin) compareUnit
          }
        }
  in
  DistributiveCombination' 
    {additive = Theory.CommutativeMonoidTheory} 
    {multiplicative = Theory.InvolutiveMonoidTheory} 
    (cast $ Fin n) freeM (Ordered.Free x_set)

TestSemiring : (DistributiveCombinationTheory CommutativeMonoidTheory InvolutiveMonoidTheory) `ModelOver` (cast $ Fin 3)
TestSemiring = InvSemiringOver 3

X0, X1, X2 : U TestSemiring .Model
X0 = TestSemiring .Env.H 0
X1 = TestSemiring .Env.H 1
X2 = TestSemiring .Env.H 2

(.+.) : U TestSemiring .Model -> U TestSemiring .Model -> U TestSemiring .Model
(.+.) = TestSemiring .Model.sem (Left Product)

(.*.) : U TestSemiring .Model -> U TestSemiring .Model -> U TestSemiring .Model
(.*.) = TestSemiring .Model.sem (Right (Mono Product))

inv : U TestSemiring .Model -> U TestSemiring .Model
inv = TestSemiring .Model.sem (Right Involution)

O1 : U TestSemiring .Model
O1 = TestSemiring .Model.sem (Left Neutral)

I1 : U TestSemiring .Model
I1 = TestSemiring .Model.sem (Right (Mono Neutral))

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

mulLftNeutrality : (I1 .*. X0) =-= X0
mulLftNeutrality = refl (I1 .*. X0)

mulRgtNeutrality : (X0 .*. I1) =-= X0
mulRgtNeutrality = refl (X0 .*. I1)

involutivity : inv (inv X0) =-= X0
involutivity = refl X0 -- SHOULD TYPECHECK

antidistributivity : inv (X0 .*. X1) =-= inv X1 .*. inv X0
antidistributivity = ?t2 -- asking for the type of the hole normalises just fine
  -- refl (inv (X0 .*. X1))

distrLeft : (X0 .*. (X1 .+. X2)) =-= ((X0 .*. X1) .+. (X0 .*. X2))
distrLeft = refl (X0 .*. (X1 .+. X2))

distrRight : ((X0 .+. X1) .*. X2) =-= ((X0 .*. X2) .+. (X1 .*. X2))
distrRight = refl ((X0 .+. X1) .*. X2)

lftAnnihilation : (O1 .*. X0) =-= O1
lftAnnihilation = refl (O1 .*. X0)

rgtAnnihilation : (X0 .*. O1) =-= O1
rgtAnnihilation = refl (X0 .*. O1)