module Frex.DistributiveCombination.Properties

import Frex.DistributiveCombination.Theory
import Frex.DistributiveCombination.Structure

import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Free

import Data.Setoid
import Data.Vect


%default total

public export
injAddPreservesEq : {additive, multiplicative : Presentation} ->
  {x : Setoid} ->
  {free_A : (Y : Setoid) -> Free additive Y} -> {free_M : (Y : Setoid) -> Free multiplicative Y} ->
  (eq : Equation additive.signature) ->
  let a_add : SetoidAlgebra additive.signature
      a_add = (free_A (cast (free_M x).Data.Model)).Data.Model.Algebra
      a_prod : SetoidAlgebra (CoproductSignature additive.signature multiplicative.signature)
      a_prod = DistributiveCombinationStructure x free_A free_M
  in
  ValidatesEquation eq a_add ->
  ValidatesEquation (injAddEq {multiplicativeSig = multiplicative.signature} eq) a_prod
injAddPreservesEq (MkEq support (Done x) (Done y)) valid env = valid env
injAddPreservesEq (MkEq support (Done x) (Call g ys)) valid env = ?injAddPreservesEq_rhs_4
injAddPreservesEq (MkEq support (Call f xs) (Done y)) valid env = ?injAddPreservesEq_rhs_5
injAddPreservesEq (MkEq support (Call f xs) (Call g ys)) valid env = ?injAddPreservesEq_rhs_6

public export
DistributiveCombinationValidatesAxioms : {additive : Presentation}-> {multiplicative : Presentation} ->
  (X : Setoid) -> (free_A : (Y : Setoid) -> Free additive Y) -> (free_M : (Y : Setoid) -> Free multiplicative Y) ->
  Validates (DistributiveCombinationTheory additive multiplicative)
    (DistributiveCombinationStructure X free_A free_M)

DistributiveCombinationValidatesAxioms x free_A free_M (AddAx ax) env =
  let freeM : Free multiplicative x
      freeM = free_M x
      freeA : Free additive (cast freeM.Data.Model)
      freeA = free_A $ cast freeM.Data.Model
  in injAddPreservesEq {free_A} {free_M} (additive.axiom ax) (freeA.Data.Model.Validate ax) env
  
DistributiveCombinationValidatesAxioms x free_A free_M (MulAx ax) env = 
  ?DistributiveCombinationValidatesAxioms_rhs_1

DistributiveCombinationValidatesAxioms x free_A free_M (DistAx ax) env = 
  ?DistributiveCombinationValidatesAxioms_rhs_2


public export
DistributiveCombination : {additive : Presentation} -> {multiplicative : Presentation} ->
  (X : Setoid) -> (free_A : (Y : Setoid) -> Free additive Y) -> (free_M : (Y : Setoid) -> Free multiplicative Y) ->
  (DistributiveCombinationTheory additive multiplicative) `ModelOver` X
DistributiveCombination x free_A free_M = 
  let freeM : Free multiplicative x
      freeM = free_M x
      freeA : Free additive (cast freeM.Data.Model)
      freeA = free_A $ cast freeM.Data.Model
  in
  MkModelOver
  { Model = MkModel
            { Algebra  = DistributiveCombinationStructure x free_A free_M
            , Validate = DistributiveCombinationValidatesAxioms x free_A free_M
            }
  , Env = freeA.Data.Env . freeM.Data.Env
  }
