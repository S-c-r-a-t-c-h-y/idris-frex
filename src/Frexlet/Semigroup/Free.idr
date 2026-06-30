module Frexlet.Semigroup.Free

import Data.Unit

import Frex
import Frexlet.Semigroup.Theory
import Frexlet.Semigroup.Frex

%default total

||| The trivial algebra with carrier the void type
public export
TrivialAlgebra : Algebra Signature
TrivialAlgebra
  = MakeAlgebra
  { U = Void
  , Semantics = \op,env => case op of
      MkOp Product => index 0 env
  }

||| The trivial semigroup with carrier the void type
public export
TrivialSemigroup : Semigroup
TrivialSemigroup =
 MkModel
  { Algebra = cast TrivialAlgebra
  , Validate = \case
      Associativity => \_ => Refl
  }

||| The free semigroup (over the empty setoid) is the trivial semigroup
public export
FreeSemigroupVoid : Free SemigroupTheory (cast Void)
FreeSemigroupVoid = 
  MkFree
  { Data = MkModelOver
      { Model = TrivialSemigroup
      , Env = mate $ id
      }
  , UP   = IsFree
    { Exists = \other => MkHomomorphism
        { H = MkSetoidHomomorphism
            { H = mate $ \_ impossible
            , preserves = \case
                MkOp Product => \[_, _] impossible
            }
        , preserves = \case _ impossible
        }
    , Unique = \_, _, _, void => absurd void
    }
  }

public export
FreeSemigroupOver : (s : Setoid) -> Free SemigroupTheory s
FreeSemigroupOver s = ByFrex FreeSemigroupVoid
                          (SemigroupFrex TrivialSemigroup s)

||| A free semigroup built out of n variables
public export
FreeSemigroup : (n : Nat) -> Semigroup
FreeSemigroup n = (FreeSemigroupOver $ cast $ Fin n).Data.Model

public export
SyntacticFrex : (n : Nat) -> Frex (FreeSemigroup n) (cast $ Fin 0)
SyntacticFrex n = Construction.Frex (FreeSemigroup n) (cast $ Fin 0)

public export
SyntacticExtension : (n : Nat) -> Extension (FreeSemigroup n) (cast $ Fin 0)
SyntacticExtension n = (SyntacticFrex n).Data

public export
SyntacticSemigroup : (n : Nat) -> Semigroup
SyntacticSemigroup n = (SyntacticExtension n).Model
