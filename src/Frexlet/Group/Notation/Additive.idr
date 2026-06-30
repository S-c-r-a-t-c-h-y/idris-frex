||| Additive notation for working with groups (mostly boilerplate)
module Frexlet.Group.Notation.Additive

import Frex

import Frexlet.Group.Theory
import public Notation.Additive

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
  cast : (a : Group) -> HVect [0 `ary` U a, 2 `ary` U a]
  cast a = cast (a.Algebra)

public export
(.Additive1) : (group : Group) -> Additive1 (U group)
group.Additive1 = MkAdditive1 (group.sem (Mono Neutral)) (group.sem (Mono Product))

public export
(.Additive2) : (group : Group) -> Additive2 (U group)
group.Additive2 = MkAdditive2 (group.sem (Mono Neutral)) (group.sem (Mono Product))

public export
(.Additive3) : (group : Group) -> Additive3 (U group)
group.Additive3 = MkAdditive3 (group.sem (Mono Neutral)) (group.sem (Mono Product))

%hint
public export
notationAdd1 : Additive1 (Term Signature x)
notationAdd1= MkAdditive1
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))

%hint
public export
notationAdd2 : Additive2 (Term Signature x)
notationAdd2 = MkAdditive2
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))

%hint
public export
notationAdd3 : Additive3 (Term Signature x)
notationAdd3 = MkAdditive3
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))
