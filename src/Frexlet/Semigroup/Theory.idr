||| The syntax and axioms for semigroups
module Frexlet.Semigroup.Theory

import Decidable.Equality
import Frex

%default total

public export
data Operation : Nat -> Type where
  Product : Operation 2

public export
Signature : Signature
Signature = MkSignature Operation

public export
data Axiom = Associativity

public export
SemigroupTheory : Presentation
SemigroupTheory = MkPresentation Theory.Signature
                                 Theory.Axiom $ \case
    Associativity => associativity         Product

public export
SemigroupAffine : AffinePresentation SemigroupTheory
SemigroupAffine = 
  MkAffinePresentation $ \case 
  Associativity =>
    MkAffineEq
      { lhsAffine = [lte1 1, lte1 1, lte1 1]
      , rhsAffine = [lte1 1, lte1 1, lte1 1]
      } 

public export
SemigroupStructure : Type
SemigroupStructure =
  SetoidAlgebra Signature

public export
Semigroup : Type
Semigroup = Model SemigroupTheory

public export
Prod : Op Signature
Prod = MkOp Product

export
Show (Op Signature) where
  show (MkOp Product) = "Product"

export
Finite (Op Signature) where
  enumerate = [Prod]

export
DecEq (Op Signature) where
  decEq (MkOp Product) (MkOp Product) = Yes Refl

export
Eq (Op Signature) where
  MkOp Product == MkOp Product = True

export
Ord (Op Signature) where
  compare (MkOp Product) (MkOp Product) = EQ

export
Finite Axiom where
  enumerate = [ Associativity ]

export
[Raw] Show Axiom where
  show = \case
    Associativity => "Associativity"

export
[Words] Show Axiom where
  show = \case
    Associativity => "Associativity"

export
ascii : Printer Signature Unit
ascii = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = asciiShow
  , opPrec     = asciiPrec
  , topParens  = False
  , opParens   = False
  } where

  [asciiPrec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [asciiShow] Show (Op Signature) where
    show (MkOp Product) = "<>"

export
generic : Printer Signature Unit
generic = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = genericShow
  , opPrec     = genericPrec
  , topParens  = False
  , opParens   = False
  } where

  [genericPrec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixR 0)

  [genericShow] Show (Op Signature) where
    show (MkOp Product) = "•"

export
natPlus : Printer Signature Unit
natPlus = MkPrinter
  { carrier    = "Nat"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = natPlusShow
  , opPrec     = natPlusPrec
  , topParens  = False
  , opParens   = False
  } where

  [natPlusPrec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [natPlusShow] Show (Op Signature) where
    show (MkOp Product) = "+"

export
additive1 : Printer Signature Unit
additive1 = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = additive1Show
  , opPrec     = additive1Prec
  , topParens  = False
  , opParens   = False
  } where

  [additive1Prec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [additive1Show] Show (Op Signature) where
    show (MkOp Product) = ".+."

export
additive2 : Printer Signature Unit
additive2 = MkPrinter
  { carrier    = "a"
  , varShow    = %search
  , opPatterns = %search
  , opShow     = additive2Show
  , opPrec     = additive2Prec
  , topParens  = False
  , opParens   = False
  } where

  [additive2Prec] HasPrecedence Signature where
    OpPrecedence Product = Just (InfixL 8)

  [additive2Show] Show (Op Signature) where
    show (MkOp Product) = ":+:"

export
withRaw : Printer Signature a -> Printer SemigroupTheory a
withRaw = MkPrinter "SemigroupTheory" Raw

export
withWords : Printer Signature a -> Printer SemigroupTheory a
withWords = MkPrinter "SemigroupTheory" Words
