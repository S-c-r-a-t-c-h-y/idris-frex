module Frexlet.Group.Notation

import public Frexlet.Group.Notation.Multiplicative

import Frex
import Frexlet.Group.Theory

public export
(.inv) : (group : Group) -> U group -> U group
group.inv = group.sem Inverse