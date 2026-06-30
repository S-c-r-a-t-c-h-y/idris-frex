||| The structure of the frex for (mere) semigroups
||| Its elements are given by non-empty lists of alternating elements
|||
||| an, xn, ..., x1
|||
||| [an, xn, ..., ]
module Frexlet.Semigroup.Frex.Structure

import Frex

import Frexlet.Semigroup.Theory

import Data.List
import Data.List1

import Data.Setoid.Pair
import Data.Setoid.List1

%default total

public export
data Side = Vars | Conc

public export
data MonNE : Side -> Type -> Type -> Type where
  OneVars  : List1 pen -> MonNE Vars pen c
  OneConc  : c -> MonNE Conc pen c

  ConsVars : List1 pen -> MonNE Conc pen c -> MonNE Vars pen c
  ConsConc : c -> MonNE Vars pen c -> MonNE Conc pen c

%name MonNE is, js, ks, ells

public export
data Mon : Type -> Type -> Type where
  MkVars : MonNE Vars pen c -> Mon pen c
  MkConc : MonNE Conc pen c -> Mon pen c

%name Mon is, js, ks, ells

public export
Cast (MonNE Vars pen c) (Mon pen c) where
  cast = MkVars

public export
Cast (MonNE Conc pen c) (Mon pen c) where
  cast = MkConc

public export
prependConc : (sg : Semigroup) -> U sg -> Mon pen (U sg) -> MonNE Conc pen (U sg)
prependConc sg x (MkVars ys) = ConsConc x ys
prependConc sg x (MkConc (OneConc y)) = OneConc (sg.sem Product x y)
prependConc sg x (MkConc (ConsConc y ys)) = ConsConc (sg.sem Product x y) ys

public export
prependVars : {sg : Semigroup} -> List1 pen -> Mon pen (U sg) -> MonNE Vars pen (U sg)
prependVars xs (MkVars (OneVars ys)) = OneVars (xs ++ ys)
prependVars xs (MkVars (ConsVars ys rest)) = ConsVars (xs ++ ys) rest
prependVars xs (MkConc ys) = ConsVars xs ys

public export
(++) : {sg : Semigroup} -> Mon pen (U sg) -> Mon pen (U sg) -> Mon pen (U sg)
(++) (MkVars (OneVars xs)) ys = MkVars $ prependVars xs ys
(++) (MkVars (ConsVars xs rest)) ys =
  MkVars $ prependVars xs (assert_smaller (MkVars (ConsVars xs rest)) (MkConc rest) ++ ys)
(++) (MkConc (OneConc x)) ys = MkConc $ prependConc sg x ys
(++) (MkConc (ConsConc x rest)) ys =
  MkConc $ prependConc sg x (assert_smaller (MkConc (ConsConc x rest)) (MkVars rest) ++ ys)


namespace Equality

  public export
  data MonNEEquality :
          {pen, ult : Type} ->
          (penRel : List1 pen -> List1 pen -> Type) ->
          (ultRel : ult -> ult -> Type) ->
          {s : Side} ->
          (xs, ys : MonNE s pen ult) -> Type where
    [search penRel ultRel]
    EqOneVars : {x, y : List1 pen} -> penRel x y ->
                MonNEEquality penRel ultRel (OneVars x) (OneVars y)
    EqOneConc : {x, y : ult} -> ultRel x y ->
                MonNEEquality penRel ultRel (OneConc x) (OneConc y)
    EqConsVars : {x, y : List1 pen} -> penRel x y ->
                MonNEEquality penRel ultRel xs ys ->
                MonNEEquality penRel ultRel (ConsVars x xs) (ConsVars y ys)
    EqConsConc : {x, y : ult} -> ultRel x y ->
                MonNEEquality penRel ultRel xs ys ->
                MonNEEquality penRel ultRel (ConsConc x xs) (ConsConc y ys)

  public export 
  data MonEquality : 
      {pen, ult : Type} -> (penRel : List1 pen -> List1 pen -> Type)
    -> (ultRel : ult -> ult -> Type) -> (is, js : Mon pen ult) -> Type where
    [search penRel ultRel]
    EqVars : MonNEEquality penRel ultRel xs ys ->
             MonEquality penRel ultRel (MkVars xs) (MkVars ys)
    EqConc : MonNEEquality penRel ultRel xs ys ->
             MonEquality penRel ultRel (MkConc xs) (MkConc ys)

  ----------------- Reflexivity --------------------------
  public export
  MonNEReflexive : {s : Side} -> (pen, ult : Setoid) -> (is : MonNE s (U pen) (U ult))
    -> MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is is
  MonNEReflexive pen ult (OneVars xs) = EqOneVars ((List1Setoid pen).equivalence.reflexive xs)
  MonNEReflexive pen ult (OneConc x) = EqOneConc $ ult.equivalence.reflexive x
  MonNEReflexive pen ult (ConsVars xs x) = 
    EqConsVars ((List1Setoid pen).equivalence.reflexive xs) (MonNEReflexive pen ult x) 
  MonNEReflexive pen ult (ConsConc x y) =
    EqConsConc (ult.equivalence.reflexive x) (MonNEReflexive pen ult y)


  public export
  MonReflexive :
    (pen, ult : Setoid) -> (is : Mon (U pen) (U ult))
    -> MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is is
  MonReflexive pen ult (MkVars x) = EqVars $ MonNEReflexive pen ult x
  MonReflexive pen ult (MkConc x) = EqConc $ MonNEReflexive pen ult x

  ----------------- Symmetry --------------------------
  public export
  MonNESymmetric : {s : Side} -> (pen, ult : Setoid) -> (is, js : MonNE s (U pen) (U ult)) 
  -> (prf : MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is js)
  -> MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation js is
  MonNESymmetric pen ult (OneVars xs) (OneVars ys) (EqOneVars prf) =
    EqOneVars $ (List1Setoid pen).equivalence.symmetric xs ys prf
  MonNESymmetric pen ult (OneConc x) (OneConc y) (EqOneConc prf) = 
    EqOneConc $ ult.equivalence.symmetric x y prf
  MonNESymmetric pen ult (ConsVars xs x) (ConsVars ys y) (EqConsVars prf1 prf2) = 
    EqConsVars ((List1Setoid pen).equivalence.symmetric xs ys prf1) 
      (MonNESymmetric pen ult x y prf2)
  MonNESymmetric pen ult (ConsConc x y) (ConsConc z w) (EqConsConc prf1 prf2) =
    EqConsConc (ult.equivalence.symmetric x z prf1) $ MonNESymmetric pen ult y w prf2

  public export
  MonSymmetric : (pen, ult : Setoid) -> (is, js : Mon (U pen) (U ult))
  -> (prf : MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is js)
  -> MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation js is
  MonSymmetric pen ult (MkVars xs) (MkVars ys) (EqVars prf) = 
    EqVars $ MonNESymmetric pen ult xs ys prf
  MonSymmetric pen ult (MkConc xs) (MkConc ys) (EqConc prf) = 
    EqConc $ MonNESymmetric pen ult xs ys prf

  ----------------- Transitivity -----------------------
  public export
  MonNETransitive : {s : Side} -> (pen, ult : Setoid) -> (is, js, ks : MonNE s (U pen) (U ult))
  -> (prf1 : MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is js)
  -> (prf2 : MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation js ks)
  -> MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is ks
  MonNETransitive pen ult (OneVars xs) (OneVars ys) (OneVars zs) (EqOneVars prf1) (EqOneVars prf2) =
    EqOneVars $ (List1Setoid pen).equivalence.transitive xs ys zs prf1 prf2
  MonNETransitive pen ult (OneConc x) (OneConc y) (OneConc z) (EqOneConc prf1) (EqOneConc prf2) =
    EqOneConc $ ult.equivalence.transitive x y z prf1 prf2
  MonNETransitive pen ult (ConsVars xs x) (ConsVars ys y) (ConsVars zs z) (EqConsVars prf1 prf2) (EqConsVars prf3 prf4) =
    EqConsVars ((List1Setoid pen).equivalence.transitive xs ys zs prf1 prf3) (MonNETransitive pen ult x y z prf2 prf4)
  MonNETransitive pen ult (ConsConc x y) (ConsConc z w) (ConsConc u v) (EqConsConc prf1 prf2) (EqConsConc prf3 prf4) =
    EqConsConc (ult.equivalence.transitive x z u prf1 prf3) $ MonNETransitive pen ult y w v prf2 prf4

  public export
  MonTransitive : (pen, ult : Setoid) -> (is, js, ks : Mon (U pen) (U ult)) -> 
    (prf1 : MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is js) ->
    (prf2 : MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation js ks) -> 
    MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation is ks
  MonTransitive pen ult (MkVars xs) (MkVars ys) (MkVars zs) (EqVars prf1) (EqVars prf2) =
    EqVars $ MonNETransitive pen ult xs ys zs prf1 prf2
  MonTransitive pen ult (MkConc xs) (MkConc ys) (MkConc zs) (EqConc prf1) (EqConc prf2) = 
    EqConc $ MonNETransitive pen ult xs ys zs prf1 prf2

public export
MonNESetoid : (pen, ult : Setoid) -> {s : Side} -> Setoid
MonNESetoid pen ult {s} = MkSetoid (MonNE s (U pen) (U ult)) $ MkEquivalence
  { relation   = MonNEEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation
  , reflexive  = MonNEReflexive pen ult
  , symmetric  = MonNESymmetric pen ult
  , transitive = MonNETransitive pen ult
  }

public export
MonSetoid : (pen, ult : Setoid) -> Setoid
MonSetoid pen ult = MkSetoid (Mon (U pen) (U ult))
  $ MkEquivalence
  { relation   = MonEquality (List1Setoid pen).equivalence.relation ult.equivalence.relation
  , reflexive  = MonReflexive pen ult
  , symmetric  = MonSymmetric pen ult
  , transitive = MonTransitive pen ult
  }

--------------------- Uninhabited cases for the equality of monNEs ---------------------
public export
Uninhabited (MonNEEquality penRel ultRel (OneVars x) (ConsVars y z)) where
  uninhabited _ impossible

public export
Uninhabited (MonNEEquality penRel ultRel (ConsVars x y) (OneVars z)) where
  uninhabited _ impossible

public export
Uninhabited (MonNEEquality penRel ultRel (OneConc x) (ConsConc y z)) where
  uninhabited _ impossible

public export
Uninhabited (MonNEEquality penRel ultRel (ConsConc x y) (OneConc z)) where
  uninhabited _ impossible

---------------------- Uninhabited cases for the equality of mons --------------------
public export
Uninhabited (MonEquality penRel ultRel (MkVars x) (MkConc y)) where
  uninhabited _ impossible

public export
Uninhabited (MonEquality penRel ultRel (MkConc x) (MkVars y)) where
  uninhabited _ impossible

public export
Uninhabited (MonEquality penRel ultRel (MkVars (OneVars x)) (MkVars (ConsVars y z))) where
  uninhabited (EqVars prf) = uninhabited prf

public export
Uninhabited (MonEquality penRel ultRel (MkVars (ConsVars x y)) (MkVars (OneVars z))) where
  uninhabited (EqVars prf) = uninhabited prf

public export
Uninhabited (MonEquality penRel ultRel (MkConc (OneConc x)) (MkConc (ConsConc y z))) where
  uninhabited (EqConc prf) = uninhabited prf

public export
Uninhabited (MonEquality penRel ultRel (MkConc (ConsConc x y)) (MkConc (OneConc z))) where
  uninhabited (EqConc prf) = uninhabited prf

----------------------- Congruence of the append operation -----------------------

public export
PrependVarsHomomorphism : (sg : Semigroup) -> (x : Setoid) ->
  SetoidHomomorphism
    (List1Setoid x `Pair` MonSetoid x (cast sg))
    (MonNESetoid x (cast sg))
    (Prelude.uncurry (prependVars {sg}))

PrependVarsHomomorphism sg x (xs, (MkVars (OneVars xs1))) (ys, (MkVars (OneVars xs2))) 
  (MkAnd xs_eq_ys (EqVars (EqOneVars xs1_eq_xs2))) =
  EqOneVars $ appendCongruence xs xs1 ys xs2 xs_eq_ys xs1_eq_xs2
PrependVarsHomomorphism sg x (xs, (MkVars (ConsVars js is))) (ys, (MkVars (ConsVars ks is2))) 
  (MkAnd xs_eq_ys (EqVars (EqConsVars js_eq_ks is_eq_is2))) =
  EqConsVars (appendCongruence xs js ys ks xs_eq_ys js_eq_ks) is_eq_is2
PrependVarsHomomorphism sg x (xs, (MkConc (OneConc xs1))) (ys, (MkConc (OneConc xs2))) 
  (MkAnd xs_eq_ys (EqConc (EqOneConc xs1_eq_xs2))) =
  EqConsVars xs_eq_ys (EqOneConc xs1_eq_xs2)
PrependVarsHomomorphism sg x (xs, (MkConc (ConsConc xs1 is1))) (ys, (MkConc (ConsConc xs2 is2))) 
  (MkAnd xs_eq_ys (EqConc $ EqConsConc xs1_eq_xs2 is1_eq_is2)) =
  EqConsVars xs_eq_ys (EqConsConc xs1_eq_xs2 is1_eq_is2)
PrependVarsHomomorphism _ _ (_, MkVars _) (_, MkConc _) (MkAnd _ rel) impossible
PrependVarsHomomorphism _ _ (_, MkVars (OneVars _)) (_, MkVars (ConsVars _ _)) prf =
  case prf of MkAnd _ rel => absurd rel
PrependVarsHomomorphism _ _ (_, MkVars (ConsVars _ _)) (_, MkVars (OneVars _)) prf =
  case prf of MkAnd _ rel => absurd rel
PrependVarsHomomorphism _ _ (_, MkConc (OneConc _)) (_, MkConc (ConsConc _ _)) prf =
  case prf of MkAnd _ rel => absurd rel
PrependVarsHomomorphism _ _ (_, MkConc (ConsConc _ _)) (_, MkConc (OneConc _)) prf =
  case prf of MkAnd _ rel => absurd rel


public export
PrependConcHomomorphism : (sg : Semigroup) -> (x : Setoid) ->
  SetoidHomomorphism
    (cast sg `Pair` MonSetoid x (cast sg))
    (MonNESetoid x (cast sg))
    (Prelude.uncurry (prependConc {sg}))

PrependConcHomomorphism sg x (i, MkConc (OneConc i1)) (j, MkConc (OneConc j1)) 
  (MkAnd i_eq_j (EqConc $ EqOneConc i1_eq_j1)) =
  EqOneConc $ sg.cong 2 (call {sig = Signature} Product (Dyn 0) (Dyn 1)) [_,_] [_,_] [i_eq_j, i1_eq_j1]
PrependConcHomomorphism sg x (i, MkConc (ConsConc i1 is1)) (j, MkConc (ConsConc j1 is2)) 
  (MkAnd i_eq_j (EqConc $ EqConsConc i1_eq_j1 is1_eq_is2)) =
  EqConsConc (sg.cong 2 (call {sig = Signature} Product (Dyn 0) (Dyn 1)) [_,_] [_,_] [i_eq_j, i1_eq_j1]) is1_eq_is2
PrependConcHomomorphism sg x (i, MkVars (OneVars xs1)) (j, MkVars (OneVars xs2)) 
  (MkAnd i_eq_j (EqVars $ EqOneVars xs1_eq_xs2)) =
  EqConsConc i_eq_j (EqOneVars xs1_eq_xs2)
PrependConcHomomorphism sg x (i, MkVars (ConsVars xs1 is1)) (j, MkVars (ConsVars xs2 is2)) 
  (MkAnd i_eq_j (EqVars $ EqConsVars xs1_eq_xs2 is1_eq_is2)) =
  EqConsConc i_eq_j (EqConsVars xs1_eq_xs2 is1_eq_is2)
PrependConcHomomorphism _ _ (_, MkVars _) (_, MkConc _) (MkAnd _ rel) impossible
PrependConcHomomorphism _ _ (_, MkVars (OneVars _)) (_, MkVars (ConsVars _ _)) prf =
  case prf of MkAnd _ rel => absurd rel
PrependConcHomomorphism _ _ (_, MkVars (ConsVars _ _)) (_, MkVars (OneVars _)) prf =
  case prf of MkAnd _ rel => absurd rel
PrependConcHomomorphism _ _ (_, MkConc (OneConc _)) (_, MkConc (ConsConc _ _)) prf =
  case prf of MkAnd _ rel => absurd rel
PrependConcHomomorphism _ _ (_, MkConc (ConsConc _ _)) (_, MkConc (OneConc _)) prf =
  case prf of MkAnd _ rel => absurd rel


public export
AppendHomomorphismProperty : (sg : Semigroup) -> (x : Setoid) ->
  (is1, is2, js1, js2 : Mon (U x) (U sg)) ->
  (MonSetoid x (cast sg)).equivalence.relation is1 is2 ->
  (MonSetoid x (cast sg)).equivalence.relation js1 js2 ->
  (MonSetoid x (cast sg)).equivalence.relation ((++) {sg} is1 js1) ((++) {sg} is2 js2)

AppendHomomorphismProperty sg x (MkVars (OneVars xs1)) (MkVars (OneVars xs2)) js1 js2 
  (EqVars (EqOneVars xs1_eq_xs2)) js1_eq_js2 = 
  EqVars $ PrependVarsHomomorphism sg x (xs1, js1) (xs2, js2) (MkAnd xs1_eq_xs2 js1_eq_js2)
AppendHomomorphismProperty sg x (MkVars (ConsVars xs1 is1)) (MkVars (ConsVars xs2 is2)) js1 js2 
  (EqVars (EqConsVars xs1_eq_xs2 is1_eq_is2)) js1_eq_js2 = 
  EqVars $ PrependVarsHomomorphism sg x (xs1, (MkConc is1 ++ js1)) (xs2, (MkConc is2 ++ js2)) 
  (MkAnd xs1_eq_xs2 (AppendHomomorphismProperty sg x
    (assert_smaller (MkVars (ConsVars xs1 is1)) (MkConc is1))
    (assert_smaller (MkVars (ConsVars xs2 is2)) (MkConc is2))
    js1 js2 (EqConc is1_eq_is2) js1_eq_js2))
AppendHomomorphismProperty sg x (MkConc (OneConc xs1)) (MkConc (OneConc xs2)) js1 js2 
  (EqConc (EqOneConc xs1_eq_xs2)) js1_eq_js2 =
  EqConc $ PrependConcHomomorphism sg x (xs1, js1) (xs2, js2) (MkAnd xs1_eq_xs2 js1_eq_js2)
AppendHomomorphismProperty sg x (MkConc (ConsConc xs1 is1)) (MkConc (ConsConc xs2 is2)) js1 js2 
  (EqConc (EqConsConc xs1_eq_xs2 is1_eq_is2)) js1_eq_js2 =
  EqConc $ PrependConcHomomorphism sg x (xs1, (MkVars is1 ++ js1)) (xs2, (MkVars is2 ++ js2))
  (MkAnd xs1_eq_xs2 (AppendHomomorphismProperty sg x
    (assert_smaller (MkConc (ConsConc xs1 is1)) (MkVars is1))
    (assert_smaller (MkConc (ConsConc xs2 is2)) (MkVars is2))
    js1 js2 (EqVars is1_eq_is2) js1_eq_js2))
AppendHomomorphismProperty _ _ (MkVars (OneVars _)) (MkVars (ConsVars _ _)) _ _ prf _ = absurd prf
AppendHomomorphismProperty _ _ (MkVars (ConsVars _ _)) (MkVars (OneVars _)) _ _ prf _ = absurd prf
AppendHomomorphismProperty _ _ (MkConc (OneConc _)) (MkConc (ConsConc _ _)) _ _ prf _ = absurd prf
AppendHomomorphismProperty _ _ (MkConc (ConsConc _ _)) (MkConc (OneConc _)) _ _ prf _ = absurd prf

public export
AppendHomomorphism : (sg : Semigroup) -> (x : Setoid) ->
  SetoidHomomorphism
    (MonSetoid x (cast sg) `Pair`
     MonSetoid x (cast sg))
    (MonSetoid x (cast sg))
    (Prelude.uncurry ((++) {sg}))
AppendHomomorphism sg x (is1,js1) (is2,js2) (MkAnd is1_eq_is2 js1_eq_js2)
  = AppendHomomorphismProperty sg x is1 is2 js1 js2 is1_eq_is2 js1_eq_js2


--------------------- Frex structure ---------------------
public export 0
FrexCarrier : (a : Semigroup) -> (s : Setoid) -> Type
FrexCarrier a s = Mon (U s) (U a)

||| Embedding of concrete elements in the frex by identifying
||| i with the singleton i
public export
(.sta) : (a : Semigroup) -> U a -> Mon x (U a)
(.sta) a y = MkConc (OneConc y)

||| Embedding variables in the frex by identifying
||| x with the singleton [x]
public export
(.dyn) : (a : Semigroup) -> x -> Mon x (U a)
(.dyn) a v = MkVars (OneVars $ v ::: Nil)

public export
FrexAlgebraStructure : (sg : Semigroup) -> (s : Setoid) -> Signature `algebraOver'` (FrexCarrier sg s)
FrexAlgebraStructure sg s Product = (++) {sg}

public export
FrexStructure : (sg : Semigroup) -> (s : Setoid) -> SemigroupStructure
FrexStructure sg s = MkSetoidAlgebra
  { algebra     = MkAlgebra (FrexCarrier sg s) (FrexAlgebraStructure sg s)
  , equivalence = (MonSetoid s (cast sg)).equivalence
  , congruence  = \case
      MkOp Product => \ [is1,js1],[is2,js2],prf => 
          AppendHomomorphism sg s (is1,js1) (is2,js2) (MkAnd (prf 0) (prf 1))
  }

public export
FrexSetoid : (a : Semigroup) -> (x : Setoid) -> Setoid
FrexSetoid a x = cast $ FrexStructure a x