module Frexlet.Group.Free.Properties

import Frex

import Frexlet.Group.Theory
import Frexlet.Group.Free.Structure

import Notation.Action

import Data.Setoid

import Syntax.PreorderReasoning.Setoid


%hide Monoid.Frex.Structure.MonAction

public export
MulLftNeutrality : {n : Nat} -> (x : FreeCarrier n) ->
  let %hint
      notation : MAction1 Nat (FreeCarrier n)
      notation = cast $ MonAction {n}
  in
  (FreeSetoid n).equivalence.relation 
    (I1 .*. x)
    x
MulLftNeutrality x = reflect (RawWordSetoid n) $ reduceFreeWord x

public export
MulRgtNeutrality : {n : Nat} -> (x : FreeCarrier n) ->
  let %hint
      notation : MAction1 Nat (FreeCarrier n)
      notation = cast $ MonAction {n}
  in
  (FreeSetoid n).equivalence.relation 
    (x .*. I1)
    x
MulRgtNeutrality x = 
  rewrite appendNilRightNeutral $ x.word in
  reflect (RawWordSetoid n) $ reduceFreeWord x

public export
MulAssociative : {n : Nat} -> (x, y, z : FreeCarrier n) ->
  let %hint
      notation : MAction1 Nat (FreeCarrier n)
      notation = cast $ MonAction {n}
  in
  (FreeSetoid n).equivalence.relation 
    (x .*. (y .*. z))
    ((x .*. y) .*. z)
MulAssociative (MkFreeCarrier [] r1) y z = 
  rewrite reduceFreeWord y in
  rewrite reduceFreeWord ((reduce (y .word ++ z .word))) in
  (FreeSetoid n).equivalence.reflexive _
MulAssociative (MkFreeCarrier (x :: xs) r1) y z = ?MulAssociative_rhs_2


public export
LftInverse : {n : Nat} -> (x : FreeCarrier n) ->
  let %hint
      notation : MAction1 Nat (FreeCarrier n)
      notation = cast $ MonAction {n}
  in
  (FreeSetoid n).equivalence.relation 
    (inv x .*. x)
    I1
LftInverse (MkFreeCarrier [] red) = []
LftInverse (MkFreeCarrier (x :: xs) red) =
  let %hint
      notation : MAction1 Nat (FreeCarrier n)
      notation = cast $ MonAction {n}
  in 
  CalcWith (RawWordSetoid n) $
  |~ (reduce ((reverse (map invLetter (x :: xs))) ++ x :: xs)) .word
  ~~ ?eq1 ... (?prf2)

public export
RgtInverse : {n : Nat} -> (x : FreeCarrier n) ->
  let %hint
      notation : MAction1 Nat (FreeCarrier n)
      notation = cast $ MonAction {n}
  in
  (FreeSetoid n).equivalence.relation 
    (x .*. inv x)
    I1


public export
FreeValidatesAxioms : {n : Nat} -> Validates GroupTheory (FreeGroupStructureOver n)
FreeValidatesAxioms (Mon LftNeutrality) env = MulLftNeutrality (env 0)
FreeValidatesAxioms (Mon RgtNeutrality) env = MulRgtNeutrality (env 0)
FreeValidatesAxioms (Mon Associativity) env = MulAssociative (env 0) (env 1) (env 2)
FreeValidatesAxioms LftInverse env = LftInverse (env 0)
FreeValidatesAxioms RgtInverse env = RgtInverse (env 0)


public export
Model : (n : Nat) -> Group
Model n = MkModel
  { Algebra  = FreeGroupStructureOver n
  , Validate = FreeValidatesAxioms
  }