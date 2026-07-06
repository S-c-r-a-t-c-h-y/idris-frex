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
  {freeM : Free multiplicative x} -> {freeA : Free additive (cast freeM.Data.Model)} ->
  (eq : Equation additive.signature) ->
  let a_add : SetoidAlgebra additive.signature
      a_add = freeA.Data.Model.Algebra
      a_prod : SetoidAlgebra (CoproductSignature additive.signature multiplicative.signature)
      a_prod = DistributiveCombinationStructure' x freeM freeA
  in
  ValidatesEquation eq a_add ->
  ValidatesEquation (injAddEq {multiplicativeSig = multiplicative.signature} eq) a_prod
injAddPreservesEq eq f env = believe_me "injAddPreservesEq"

-- injAddPreservesEq (MkEq support (Done x) (Done y)) valid env = valid env
-- injAddPreservesEq (MkEq support (Done x) (Call g ys)) valid env = ?injAddPreservesEq_rhs_4
-- injAddPreservesEq (MkEq support (Call f xs) (Done y)) valid env = ?injAddPreservesEq_rhs_5
-- injAddPreservesEq (MkEq support (Call f xs) (Call g ys)) valid env = ?injAddPreservesEq_rhs_6

public export
DistributiveCombinationValidatesAxioms : {additive : Presentation} -> {multiplicative : Presentation} ->
  (X : Setoid) -> (freeM : Free multiplicative X) -> (freeA : Free additive (cast freeM.Data.Model)) ->
  Validates (DistributiveCombinationTheory additive multiplicative)
    (DistributiveCombinationStructure' X freeM freeA)

DistributiveCombinationValidatesAxioms x freeM freeA (AddAx ax) env =
   injAddPreservesEq {freeA} {freeM} (additive.axiom ax) (freeA.Data.Model.Validate ax) env
  
DistributiveCombinationValidatesAxioms x freeM freeA (MulAx ax) env = 
  believe_me "DistributiveCombinationValidatesAxioms@MulAx"

DistributiveCombinationValidatesAxioms x freeM freeA (DistAx ax) env = 
  believe_me "DistributiveCombinationValidatesAxioms@DistAx"


public export
DistributiveCombination' : {additive : Presentation} -> {multiplicative : Presentation} ->
  (X : Setoid) -> (freeM : Free multiplicative X) -> (freeA : Free additive (cast freeM.Data.Model)) ->
  (DistributiveCombinationTheory additive multiplicative) `ModelOver` X
DistributiveCombination' x freeM freeA = 
  MkModelOver
  { Model = MkModel
            { Algebra  = DistributiveCombinationStructure' x freeM freeA
            , Validate = DistributiveCombinationValidatesAxioms x freeM freeA
            }
  , Env = freeA.Data.Env . freeM.Data.Env
  }


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
  DistributiveCombination' x freeM freeA
