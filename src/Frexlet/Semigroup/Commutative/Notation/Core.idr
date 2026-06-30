module Frexlet.Semigroup.Commutative.Notation.Core

import Frex
import Frexlet.Semigroup.Commutative.Theory

export infix 9 .*.

public export
(.sum) : (a : CommutativeSemigroup) -> Vect (S n) (U a) -> U a
(.sum) a (x :: []) = x
(.sum) a (x :: (y :: ys)) = 
  let (.*.) = a.sem Product 
  in x .*. a.sum (y :: ys)

public export
data Positive : Nat -> Type where
  Pos : Positive (S k)

public export
Uninhabited (Positive 0) where
  uninhabited _ impossible

public export
(.mult) : (a : CommutativeSemigroup) -> (n : Nat) -> {auto nz : Positive n} -> U a -> U a
(.mult) a 0 {nz} x = absurd $ uninhabited nz
(.mult) a (S k) x = a.sum $ replicate (S k) x