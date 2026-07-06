module Frex.DistributiveCombination.Construction

import Frex.DistributiveCombination.Theory
import Frex.DistributiveCombination.Structure
import Frex.DistributiveCombination.Properties

import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Free

import Data.Setoid

import Data.Vect
import Data.Vect.Quantifiers

%default total

public export
DistributiveCombinationFree : {additive : Presentation} -> {multiplicative : Presentation}
  -> (X : Setoid) -> AffinePresentation multiplicative -> CommutativeTheory additive
  -> (freeM : Free multiplicative X) -> (freeA : Free additive (cast freeM.Data.Model)) -> 
  Freeness (DistributiveCombination' X freeM freeA)
DistributiveCombinationFree x mult_affine add_comm freeM freeA = 
  believe_me "DistributiveCombinationFree"

public export
FreeDistributiveCombination' : {additive : Presentation} -> {multiplicative : Presentation} ->
  (X : Setoid) -> AffinePresentation multiplicative -> CommutativeTheory additive ->
  (freeM : Free multiplicative X) -> (freeA : Free additive (cast freeM.Data.Model)) ->
  Free (DistributiveCombinationTheory additive multiplicative) X
FreeDistributiveCombination' x mult_affine add_comm freeM freeA =
  MkFree
  { Data = DistributiveCombination' x freeM freeA
  , UP   = DistributiveCombinationFree x mult_affine add_comm freeM freeA
  }

||| Gives the free distributive combination of a multiplicative theory over an additive theory on a set X
public export
FreeDistributiveCombination : {additive : Presentation} -> {multiplicative : Presentation} -> 
  (X : Setoid) -> AffinePresentation multiplicative -> CommutativeTheory additive ->
  (free_A : (Y : Setoid) -> Free additive Y) -> (free_M : (Y : Setoid) -> Free multiplicative Y) -> 
  Free (DistributiveCombinationTheory additive multiplicative) X
FreeDistributiveCombination x mult_affine add_comm free_A free_M =
  let freeM : Free multiplicative x
      freeM = free_M x
      freeA : Free additive (cast freeM.Data.Model)
      freeA = free_A $ cast freeM.Data.Model
  in
  FreeDistributiveCombination' x mult_affine add_comm freeM freeA
