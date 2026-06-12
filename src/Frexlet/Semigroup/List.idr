||| Semigroup structures over Lists 
module Frexlet.Semigroup.List

import Frex
import Frexlet.Semigroup.Theory

import public Data.List
import public Data.Setoid.List
        
%default total

||| Semigroup structure over lists with concatenation
public export
ListSemigroup : {A:Setoid} -> Semigroup
ListSemigroup = MkModel
  { Algebra = MkSetoidAlgebra
      { algebra = MkAlgebra
        { U = List (U A)
        , Sem = \case Product => (++) }
        , equivalence = (ListSetoid A) .equivalence
        , congruence = \case
          MkOp Product => \[x1,x2], [y1,y2], idx => appendCongruence x1 x2 y1 y2 (idx 0) (idx 1) }
  , Validate = \case
      Associativity => \env => reflect (ListSetoid A) (Data.List.appendAssociative (env 0) (env 1) (env 2))
  }
