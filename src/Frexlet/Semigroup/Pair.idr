||| Semigroup structures over pairs
module Frexlet.Semigroup.Pair

import Frex
import Frex.Signature
import Frex.Algebra
import Frex.Presentation

import Frex.Model
import Frexlet.Semigroup.Theory
import Data.Setoid
import Data.Setoid.Pair

%default total

public export
assoc : {a,b,c : Setoid} -> Pair a (Pair b c) <~> Pair (Pair a b) c
assoc = MkIsomorphism fwd bwd
         (IsIsomorphism (\(x,(y,z)) => (Pair a (Pair b c)).equivalence.reflexive (x,(y,z)))
                        (\((x,y),z) => (Pair (Pair a b) c).equivalence.reflexive ((x,y),z)))
   where fwd : Pair a (Pair b c) ~> Pair (Pair a b) c
         fwd = MkSetoidHomomorphism (\abc => ((fst abc,fst (snd abc)), snd (snd abc)))
                  (\_, _, (MkAnd ap (MkAnd bp cp)) => MkAnd (MkAnd ap bp) cp)
         bwd : Pair (Pair a b) c ~> Pair a (Pair b c)
         bwd = MkSetoidHomomorphism (\abc => (fst (fst abc), (snd (fst abc), snd abc)))
                  (\_, _, (MkAnd (MkAnd ap bp) cp) => (MkAnd ap (MkAnd bp cp)))

public export
SemigroupPair : Semigroup
SemigroupPair = MkModel
  { Algebra = MkSetoidAlgebra
      { algebra = MkAlgebra
        { U = Setoid
        , Sem = \case
           Product => Pair }
      , equivalence = IsoEquivalence
      , congruence = \case
          MkOp Product => \[x1,x2], [y1,y2], idx => (pairIso (idx FZ) (idx (FS FZ))) }
  , Validate = \case Associativity => \env => assoc }
