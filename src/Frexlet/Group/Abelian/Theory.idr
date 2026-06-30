||| The syntax and axioms for groups
module Frexlet.Group.Abelian.Theory

import Frex
import Frex.Algebra

import Syntax.PreorderReasoning.Setoid

import public Frexlet.Group
import Frexlet.Group.Properties
import Frexlet.Group.Notation

%default total

%hide Monoid.Theory.Signature

private infixl 9 .*., :*:

public export
data Axiom
  = Grp Group.Theory.Axiom
  | Commutativity

public export
AbelianGroupTheory : Presentation
AbelianGroupTheory = MkPresentation Theory.Signature Abelian.Theory.Axiom $ \case
    Grp ax => (GroupTheory).axiom ax
    Commutativity => commutativity (Mono Product)


public export
AbelianGroupStructure : Type
AbelianGroupStructure = SetoidAlgebra Signature

public export
AbelianGroup : Type
AbelianGroup = Model AbelianGroupTheory

||| Smart constructor for abelian groups
public export
MkAbelianGroup
  : (group : Group) ->
    (commutativity : ValidatesEquation
                       (Axiom.commutativity {sig = Theory.Signature} (Mono Product))
                       (group.Algebra)) ->
    AbelianGroup
MkAbelianGroup group commutativity = MkModel
  { Algebra = group.Algebra
  , Validate = \case
      Grp ax        => group.Validate ax
      Commutativity => commutativity
  }

public export
Cast AbelianGroup Group where
  cast cgroup = MkModel
    { Algebra  = cgroup.Algebra
    , Validate = \ax => cgroup.Validate (Grp ax)
    }

public export
Plus : Op Signature
Plus = MkOp (Mono Product)


public export
interchange : (a : AbelianGroup) -> (x, y, z, w : U a) ->
  let (.*.) = a.sem (Mono Product) in
  a.rel
    ((x .*. z) .*. (y .*. w))
    ((x .*. y) .*. (z .*. w))
interchange a x y z w = 
  let (.*.) : U a -> U a -> U a
      (.*.) = a.sem (Mono Product)
      (:*:) = call {sig = Signature} (Mono Product)
  in
  CalcWith (cast a) $
  |~ ((x .*. z) .*. (y .*. w))
  ~~ (x .*. (z .*. (y .*. w))) ..< (a.validate (Grp $ Mon $ Associativity) [_, _, _])
  ~~ (x .*. ((z .*. y) .*. w)) ... (a.cong 1 (Sta _ :*: Dyn 0) [_] [_] [a.validate (Grp $ Mon $ Associativity) [_, _, _]])
  ~~ (x .*. ((y .*. z) .*. w)) ... (a.cong 1 (Sta _ :*: (Dyn 0 :*: Sta _)) [_] [_] [a.validate (Commutativity) [_, _]])
  ~~ (x .*. (y .*. (z .*. w))) ..< (a.cong 1 (Sta _ :*: Dyn 0) [_] [_] [a.validate (Grp $ Mon $ Associativity) [_, _, _]])
  ~~ ((x .*. y) .*. (z .*. w)) ... (a.validate (Grp $ Mon $ Associativity) [_, _, _])

public export
inverseProductAbelian : (a : AbelianGroup) -> (x, y : U a) ->
  let %hint
      notation : Multiplicative1 (U a)
      notation = (cast a).Multiplicative1
      inv : U a -> U a
      inv = a.sem Inverse
  in 
  a.rel (inv $ x .*. y) (inv x .*. inv y)
inverseProductAbelian a x y =
  a.equivalence.transitive _ _ _ 
  (inverseProduct (cast a) _ _) $
  a.validate Commutativity [_, _]

public export
AbelianGroupCommutative : CommutativeTheory AbelianGroupTheory
AbelianGroupCommutative (Mono x) (Mono y) m env with (x) | (y)
    _ | Product | Product = interchange m (env 0) (env 1) (env 2) (env 3)
    _ | Product | Neutral = m.validate (Grp $ Mon $ LftNeutrality) [_]
    _ | Neutral | Product = m.equivalence.symmetric _ _ $ m.validate (Grp $ Mon $ LftNeutrality) [_]
    _ | Neutral | Neutral = m.equivalence.reflexive _
AbelianGroupCommutative (Mono x) Inverse m env with (x)
    _ | Product = m.equivalence.symmetric _ _ $ inverseProductAbelian m _ _
    _ | Neutral = m.equivalence.symmetric _ _ $ inverseNeutral (cast m)
AbelianGroupCommutative Inverse (Mono x) m env with (x)
    _ | Product = inverseProductAbelian m _ _
    _ | Neutral = inverseNeutral (cast m)
AbelianGroupCommutative Inverse Inverse m env = m.equivalence.reflexive _


export
[Raw] Show Abelian.Theory.Axiom where
  show = \case
    Grp ax => show @{Raw} ax
    Commutativity => "Commutativity"

export
[Words] Show Abelian.Theory.Axiom where
  show = \case
    Grp ax => show @{Words} ax
    Commutativity => "Commutativity"

export
Finite Abelian.Theory.Axiom where
  enumerate = map Grp enumerate ++ [Commutativity]

export
withRaw : Printer Signature a -> Printer AbelianGroupTheory a
withRaw = MkPrinter "AbelianGroupTheory" Raw

export
withWords : Printer Signature a -> Printer AbelianGroupTheory a
withWords = MkPrinter "AbelianGroupTheory" Words
