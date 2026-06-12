||| Constructing the frex of a semigroup by a setoid
module Frexlet.Semigroup.Frex.Construction

import Frex

import Frexlet.Semigroup.Theory
import Frexlet.Semigroup.Frex.Structure
import Frexlet.Semigroup.Frex.Properties

import Data.List
import Data.List1
-- import Data.List.Elem

import Data.Setoid.Pair
import Data.Setoid.List1

import Syntax.PreorderReasoning.Generic

%default total

private infixl 9 .*., :*:

public export
reify : (sg : Semigroup) -> (s : Setoid) -> FrexCarrier sg s -> Term Signature (U sg `Either` U s)
reify sg s (MkVars (OneVars xs)) =
    let (.*.) = call {sig = Signature} Product in
    foldl1By (\acc,x => acc .*. Done (Right x)) (\x => Done (Right x)) xs
reify sg s (MkVars (ConsVars xs is)) =
    let (.*.) = call {sig = Signature} Product in
    (foldl1By (\acc,x => acc .*. Done (Right x)) (\x => Done (Right x)) xs) .*. reify sg s (assert_smaller (ConsVars xs is) (MkConc is))
reify sg s (MkConc (OneConc y)) = Done (Left y)
reify sg s (MkConc (ConsConc y is)) =
    let (.*.) = call {sig = Signature} Product in
    (Done (Left y)) .*. reify sg s (assert_smaller (MkConc (ConsConc y is)) (MkVars is))

public export
normalForm : (sg : Semigroup) -> (s : Setoid) -> (is : FrexCarrier sg s) ->
  (FrexSemigroup sg s).rel
    ((FrexSemigroup sg s).Sem (reify sg s is) (either sg.sta sg.dyn))
    is
normalForm sg s (MkVars (OneVars xs)) = ?normalForm_rhs_2
normalForm sg s (MkVars (ConsVars xs is)) = ?normalForm_rhs_3
normalForm sg s (MkConc (OneConc x)) = ?normalForm_rhs_4
normalForm sg s (MkConc (ConsConc x is)) = ?normalForm_rhs_5


public export
staIsHomo : (sg : Semigroup) -> (s : Setoid) -> Homomorphism sg.Algebra (FrexStructure sg s) (sg.sta)
staIsHomo sg s (MkOp Product) [i, j] = (FrexSetoid sg s).equivalence.reflexive _

public export
staHomo : (sg : Semigroup) -> (s : Setoid) -> (sg ~> FrexSemigroup sg s)
staHomo sg s = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
    { H           = sg.sta
    , homomorphic = \_,_,prf => EqConc $ EqOneConc prf
    }
  , preserves = staIsHomo sg s
  }

public export
dynHomo : (sg : Semigroup) -> (s : Setoid) -> (s ~> FrexSetoid sg s)
dynHomo sg s = MkSetoidHomomorphism
  { H           = sg.dyn
  , homomorphic = \_,_,prf => EqVars $ EqOneVars $ prf ::: s.ListEqualityReflexive _
  }

public export
Extension : (sg : Semigroup) -> (s : Setoid) -> Extension sg s
Extension sg s = MkExtension
  { Model = FrexSemigroup sg s
  , Embed = staHomo sg s
  , Var   = dynHomo sg s
  }

-- TODO: implement
public export
ExtenderFunction : (sg : Semigroup) -> (s : Setoid) -> Frex.ExtenderFunction (Extension sg s)


-- public export
-- ExtenderPreservesProd : (sg : Semigroup) -> (s : Setoid) ->
--   (other : Extension sg s) ->
--   (is,js : FrexCarrier sg s) ->
--   let %hint
--       (.*.) : Term Signature (U other.Model) -> Term Signature (U other.Model) -> Term Signature (U other.Model)
--       (.*.) = call {sig = Signature} Product
--       %hint
--       (:*:) : Term Signature (U sg) -> Term Signature (U sg) -> Term Signature (U sg)
--       (:*:) = call {sig = Signature} Product
--       h : U (FrexSemigroup sg s) -> U other.Model
--       h = ExtenderFunction sg s other
--   in other.Model.rel
--     (h (is :*: js) )
--     (h is .*. h js)

-- TODO: implement
public export
ExtenderIsHomomorphism : (sg : Semigroup) -> (s : Setoid) ->
  ExtenderIsHomomorphism (Extension sg s) (ExtenderFunction sg s)
ExtenderIsHomomorphism a s other (MkOp Product) [is,js] =
  ?ExtenderPreservesProd a s other is js

-- TODO: implement
public export
ExtenderIsSetoidHomomorphism : (sg : Semigroup) -> (s : Setoid) -> (other : Extension sg s) ->
  (is,js : FrexCarrier sg s) ->
  (prf : (FrexSemigroup sg s).rel is js) ->
  other.Model.rel
    (ExtenderFunction sg s other is)
    (ExtenderFunction sg s other js)

public export
ExtenderHomomorphism : (sg : Semigroup) -> (s : Setoid) -> Frex.Frex.ExtenderHomomorphism (Extension sg s)
ExtenderHomomorphism sg s other = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
      { H           = ExtenderFunction sg s other
      , homomorphic = ExtenderIsSetoidHomomorphism sg s other
      }
  , preserves = ExtenderIsHomomorphism sg s other
  }

-- TODO: implement
public export
ExtenderPreservesEmbedding : (sg : Semigroup) -> (s : Setoid) ->
  ExtenderPreservesEmbedding (Extension sg s) (ExtenderHomomorphism sg s)

-- TODO: implement
public export
ExtenderPreservesVars : (sg : Semigroup) -> (s : Setoid) ->
  ExtenderPreservesVars (Extension sg s) (ExtenderHomomorphism sg s)

public export
Extender : (sg : Semigroup) -> (s : Setoid) -> Extender (Extension sg s)
Extender sg s other = MkExtensionMorphism
  { H             = ExtenderHomomorphism       sg s other
  , PreserveEmbed = ExtenderPreservesEmbedding sg s other
  , PreserveVar   = ExtenderPreservesVars      sg s other
  }

-- TODO: implement
public export
Uniqueness : (sg : Semigroup) -> (s : Setoid) -> Uniqueness (Extension sg s)

public export
SemigroupFrex : (sg : Semigroup) -> (s : Setoid) -> Frex sg s
SemigroupFrex sg s = MkFrex 
  { Data = Extension sg s
  , UP   = IsUniversal
    { Exists = Extender sg s
    , Unique = Uniqueness sg s
    }
  }

public export
SemigroupFrexlet : Frexlet {pres = SemigroupTheory}
SemigroupFrexlet sg {n} = SemigroupFrex sg (cast $ Fin n)