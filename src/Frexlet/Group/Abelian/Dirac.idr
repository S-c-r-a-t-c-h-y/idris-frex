||| Properties relating to Kronecker's delta function, also known as
||| Dirac's delta distribution
module Frexlet.Group.Abelian.Dirac

import Frex

import Data.Vect.Properties

import Syntax.PreorderReasoning.Generic
import Syntax.PreorderReasoning

import Decidable.Equality
import Data.Bool.Decidable

import Frexlet.Group.Abelian.IntInd

%default total

export
easyDec : DecEq a => (x : a) -> decEq x x = Yes Refl
easyDec  x with (decEq x x)
 easyDec x | Yes Refl  = Refl
 easyDec x | No contra = void $ contra Refl


public export
dirac : (i, j : Fin n) -> IntInd
dirac i j = case (decEq i j) of
  Yes _ => 1
  No  _ => 0

export
diracOnDiagonal : (i : Fin n) -> dirac i i = 1
diracOnDiagonal i = Calc $
  |~ dirac i i
  ~~ 1 ...(cong (\u => case u of {Yes _ => 1 ; No  _ => 0})
                (easyDec i))
export
diracOffDiagonal : (i,j : Fin n) -> Not (i = j) -> dirac i j = 0
diracOffDiagonal  i j neq with (decEq i j)
 diracOffDiagonal i j neq | Yes eq = void (neq eq)
 diracOffDiagonal i j neq | No  _  = Refl

export
diracSym : {0 n : Nat} -> (i, j : Fin n) -> dirac i j = dirac j i
diracSym  i j with (decEq i j)
 diracSym i i | Yes Refl   = sym $ diracOnDiagonal    i
 diracSym i j | No i_neq_j = sym $ diracOffDiagonal j i (negEqSym i_neq_j)
