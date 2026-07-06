module Frexlet.Group.Abelian.Notation.Core

import Frex
import Frexlet.Group.Abelian.Theory
import Frexlet.Group.Abelian.NZInt

import public Notation
import public Notation.Action
import public Data.Vect.Quantifiers

%default total

%hide Monoid.Theory.Signature

namespace Algebra
  public export
  cast : (a : GroupStructure) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = [ a.sem (Mono Neutral)
           , a.sem (Mono Product)
           ]

namespace Model
  public export
  cast : (a : AbelianGroup) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = cast (a.Algebra)

public export
(.sum) : (a : AbelianGroup) -> Vect n (U a) -> U a
(.sum) a xs = let _ : Additive1 (U a) = Prelude.cast (Core.Model.cast a) in
  case xs of
    [] => O1
    (x :: xs) => x .+. a.sum xs

public export
mult : (a : AbelianGroup) -> NZInt -> U a -> U a
mult a (Pos k) x = a.sum $ replicate (S k) x
mult a (Neg k) x = a.sum $ replicate (S k) (a.sem Inverse x)

public export
NatActionData : (a : AbelianGroup) -> ActionData NZInt (U a)
NatActionData a = mult a :: cast a

public export
NatAction1 : (a : AbelianGroup) -> Action1 NZInt (U a)
NatAction1 a = cast (NatActionData a)

public export
NatAction2 : (a : AbelianGroup) -> Action2 NZInt (U a)
NatAction2 a = cast (NatActionData a)

%hint
public export
notation2 : Action2 NZInt (Term Signature (a `Either` (Fin n)))
notation2 = NatAction2 (F _ (irrelevantCast (a `Either` (Fin n))))

%hint
public export
notation1 : Action1 NZInt (Term Signature (a `Either` (Fin n)))
notation1 = NatAction1 (F _ (irrelevantCast (a `Either` (Fin n))))