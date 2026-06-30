||| Multiplicative notation for working with groups (mostly boilerplate)
module Frexlet.Group.Notation.Multiplicative

import Frex

import Frexlet.Group.Theory

import public Notation.Multiplicative

%default total

%hide Monoid.Theory.Signature

public export
(.Multiplicative1) : (group : Group) -> Multiplicative1 (U group)
group.Multiplicative1 = MkMultiplicative1 (group.sem (Mono Neutral)) (group.sem (Mono Product))

public export
(.Multiplicative2) : (group : Group) -> Multiplicative2 (U group)
group.Multiplicative2 = MkMultiplicative2 (group.sem (Mono Neutral)) (group.sem (Mono Product))

public export
(.Multiplicative3) : (group : Group) -> Multiplicative3 (U group)
group.Multiplicative3 = MkMultiplicative3 (group.sem (Mono Neutral)) (group.sem (Mono Product))

public export
notationSyntax : Multiplicative1 (Term Signature x)
notationSyntax = MkMultiplicative1
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))
%hint
public export
notation1 : Multiplicative1 (Term Signature x)
notation1 = MkMultiplicative1
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))

%hint
public export
notation2 : Multiplicative2 (Term Signature x)
notation2 = MkMultiplicative2
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))

%hint
public export
notation3 : Multiplicative3 (Term Signature x)
notation3 = MkMultiplicative3
              (call {sig = Signature} (Mono Neutral))
              (call {sig = Signature} (Mono Product))
