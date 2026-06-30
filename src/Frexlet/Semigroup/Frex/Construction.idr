||| Constructing the frex of a semigroup by a setoid
module Frexlet.Semigroup.Frex.Construction

import Frex

import Frexlet.Semigroup.Theory
import Frexlet.Semigroup.Frex.Structure
import Frexlet.Semigroup.Frex.Properties

import Data.List
import Data.List1

import Data.Setoid.List1

import Syntax.PreorderReasoning.Setoid

%default total

private infixl 9 .*., :*:

public export
foldProduct : (prod : a -> a -> a) -> (terms : List1 a) -> a
foldProduct prod (head ::: []) = head
foldProduct prod (head ::: (y :: xs)) =
  let (.*.) = prod in
  head .*. foldProduct prod (assert_smaller (head ::: (y :: xs)) (y ::: xs))

-- TODO: rewrite using a : Semigroup
public export
foldProductHomomorphism : {a : Setoid} -> (prod : U a -> U a -> U a) -> 
  (xs, ys : List1 (U a)) -> (xs_eq_ys : a.List1Equality xs ys) ->
  (prodHomomorphism : (x, y, z, w : U a) -> 
    (x_eq_y : a.equivalence.relation x y) -> 
    (z_eq_w : a.equivalence.relation z w) ->
    a.equivalence.relation (prod x z) (prod y w)) ->
  a.equivalence.relation (foldProduct prod xs) (foldProduct prod ys)
foldProductHomomorphism prod (x ::: []) (y ::: []) (hdEq ::: _) _ = hdEq
foldProductHomomorphism _ (_ ::: []) (_ ::: (_ :: _)) (_ ::: []) _ impossible
foldProductHomomorphism _ (_ ::: (_ :: _)) (_ ::: []) (_ ::: []) _ impossible
foldProductHomomorphism prod (x ::: (z :: xs)) (y ::: (w :: ys)) (hdEq ::: (z_eq_w :: xs_eq_ys)) prodHomo = 
  prodHomo _ _ _ _ hdEq $ 
  foldProductHomomorphism _ 
    (assert_smaller (x ::: (z :: xs)) (z ::: xs)) 
    (assert_smaller (y ::: (w :: ys)) (w ::: ys)) 
    (z_eq_w ::: xs_eq_ys) prodHomo

public export
foldProductSplit : {a : Semigroup} ->
  (x, y : U a) -> (xs, ys : List $ U a) ->
  let (.*.) = a.sem Product in
  a.equivalence.relation
    (foldProduct (.*.) (x ::: xs ++ (y :: ys)))  
    ((foldProduct (.*.) (x ::: xs)) .*. (foldProduct (.*.) (y ::: ys)))
foldProductSplit x y [] ys = a.equivalence.reflexive _
foldProductSplit x y (z :: zs) ys = 
  let (.*.) : U a -> U a -> U a
      (.*.) = a.sem Product
      (:*:) : Term Signature (U a `Either` Fin 1) -> 
              Term Signature (U a `Either` Fin 1) -> 
              Term Signature (U a `Either` Fin 1)
      (:*:) = call {sig = Signature} Product
  in
  CalcWith (cast a) $
  |~ x .*. foldProduct (.*.) (z ::: zs ++ (y :: ys))
  ~~ x .*. (foldProduct (.*.) (z ::: zs) .*. foldProduct (.*.) (y ::: ys)) 
          ... (a.cong 1 (Sta _ :*: Dyn 0) [_] [_] [foldProductSplit z y zs ys])
  ~~ (x .*. foldProduct (.*.) (z ::: zs)) .*. foldProduct (.*.) (y ::: ys) 
          ... (a.validate Associativity [_, _, _])

public export
foldProductSplit1 : {a : Semigroup} ->
  (xs, ys : List1 $ U a) ->
  let (.*.) = a.sem Product in
  a.equivalence.relation
    (foldProduct (.*.) (xs ++ ys))  
    ((foldProduct (.*.) xs) .*. (foldProduct (.*.) ys))
foldProductSplit1 (x ::: xs) (y ::: ys) = foldProductSplit x y xs ys

public export
reify : (sg : Semigroup) -> (s : Setoid) -> FrexCarrier sg s -> Term Signature (U sg `Either` U s)
reify sg s (MkVars (OneVars xs)) =
    foldProduct (call {sig = Signature} Product) (map (Done . Right) xs)
reify sg s (MkVars (ConsVars xs is)) =
    let (.*.) = call {sig = Signature} Product in
    (foldProduct (.*.) (map (Done . Right) xs)) .*. reify sg s (assert_smaller (ConsVars xs is) (MkConc is))
reify sg s (MkConc (OneConc y)) = Done (Left y)
reify sg s (MkConc (ConsConc y is)) =
    let (.*.) = call {sig = Signature} Product in
    (Done (Left y)) .*. reify sg s (assert_smaller (MkConc (ConsConc y is)) (MkVars is))


public export
normalFormOneVars : (sg : Semigroup) -> (s : Setoid) -> (xs : List1 (U s)) ->
  (FrexSemigroup sg s).rel
    ((FrexSemigroup sg s).Sem (reify sg s (MkVars $ OneVars xs)) (either sg.sta sg.dyn))
    (MkVars (OneVars xs))
normalFormOneVars sg s (head ::: []) = (FrexSetoid sg s).equivalence.reflexive _
normalFormOneVars sg s (head ::: (x :: xs)) = 
  let frex : Semigroup
      frex = FrexSemigroup sg s
      env : (U sg `Either` U s) -> U frex
      env = either sg.sta sg.dyn
  in
  CalcWith (cast frex) $
  |~ frex.Sem (reify sg s (MkVars $ OneVars (head ::: (x :: xs)))) env
  ~~ MkVars (prependVars {sg} (head ::: []) 
            (frex.Sem (reify sg s (MkVars $ OneVars (x ::: xs))) env)) .=. (Refl)
  ~~ MkVars (prependVars {sg} (head ::: []) (MkVars $ OneVars (x ::: xs))) 
          ... (EqVars $ prependVarsCong {sg} _ _ _ 
              (normalFormOneVars sg s (assert_smaller (head ::: (x :: xs)) (x ::: xs))))
  ~~ MkVars (OneVars ((head ::: []) ++ (x ::: xs))) .=. (Refl)
  ~~ MkVars (OneVars (head ::: (x :: xs))) .=. (Refl)


public export
normalForm : (sg : Semigroup) -> (s : Setoid) -> (is : FrexCarrier sg s) ->
  (FrexSemigroup sg s).rel
    ((FrexSemigroup sg s).Sem (reify sg s is) (either sg.sta sg.dyn))
    is
normalForm sg s (MkVars (OneVars xs)) = 
  normalFormOneVars sg s xs
normalForm sg s (MkVars (ConsVars xs is)) = 
  let frex : Semigroup
      frex = FrexSemigroup sg s
      (.*.) : U frex -> U frex -> U frex
      (.*.) = frex.sem Product
      (:*:) : Term Signature (U frex `Either` Fin 2) -> 
              Term Signature (U frex `Either` Fin 2) -> 
              Term Signature (U frex `Either` Fin 2)
      (:*:) = call {sig = Signature} Product
  in CalcWith (cast frex) $
  |~ frex.Sem (reify sg s (MkVars (ConsVars xs is))) (either sg.sta sg.dyn)
  ~~ MkVars (OneVars xs) .*. MkConc is 
        ... (frex.cong 2 (Dyn 0 :*: Dyn 1) [_,_] [_,_] 
            [normalFormOneVars sg s xs, normalForm sg s 
            (assert_smaller (MkVars (ConsVars xs is)) (MkConc is))])
  ~~ MkVars (ConsVars xs is) .=. (Refl)
normalForm sg s (MkConc (OneConc x)) = (FrexSetoid sg s).equivalence.reflexive _
normalForm sg s (MkConc (ConsConc x is)) = 
  let frex : Semigroup
      frex = FrexSemigroup sg s
      (.*.) : U frex -> U frex -> U frex
      (.*.) = frex.sem Product
      (:*:) : Term Signature (U frex `Either` Fin 1) -> 
              Term Signature (U frex `Either` Fin 1) -> 
              Term Signature (U frex `Either` Fin 1)
      (:*:) = call {sig = Signature} Product
  in CalcWith (cast frex) $
  |~ MkConc (OneConc x) .*. frex.Sem (reify sg s (MkVars is)) (either sg.sta sg.dyn)
  ~~ MkConc (OneConc x) .*. MkVars is 
        ... (frex.cong 1 (Sta (MkConc (OneConc x)) :*: Dyn 0) [_] [_] 
            [normalForm sg s (assert_smaller (MkConc (ConsConc x is)) (MkVars is))])
  ~~ MkConc (ConsConc x is) .=. (Refl)


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

public export
ExtenderFunction : (sg : Semigroup) -> (s : Setoid) -> Frex.ExtenderFunction (Extension sg s)
ExtenderFunction sg s other (MkVars (OneVars xs)) = 
  foldProduct (other.Model.sem Product) (map (other.Var.H) xs)
ExtenderFunction sg s other (MkVars (ConsVars xs is)) = 
  let (.*.) = other.Model.sem Product in
  (foldProduct (.*.) (map (other.Var.H) xs)) .*. 
  (ExtenderFunction sg s other (assert_smaller (MkVars (ConsVars xs is)) (MkConc is)))
ExtenderFunction sg s other (MkConc (OneConc x)) =
  other.Embed.H.H x
ExtenderFunction sg s other (MkConc (ConsConc x is)) = 
  let (.*.) = other.Model.sem Product in
  (other.Embed.H.H x) .*. 
  (ExtenderFunction sg s other (assert_smaller (MkConc (ConsConc x is)) (MkVars is)))

public export
ExtenderPreservesConcat : (sg : Semigroup) -> (s : Setoid) ->
  (other : Extension sg s) -> (xs, ys : List1 (U s)) ->
  let (.*.) = other.Model.sem Product in
  other.Model.rel
    (ExtenderFunction sg s other (MkVars . OneVars $ xs ++ ys))
    (ExtenderFunction sg s other (MkVars . OneVars $ xs) .*. ExtenderFunction sg s other (MkVars . OneVars $ ys))   
ExtenderPreservesConcat sg s other (x ::: xs) (y ::: ys) =
  let (.*.) : U (cast other.Model) -> U (cast other.Model) -> U (cast other.Model)
      (.*.) = other.Model.sem Product
  in
  CalcWith (cast other.Model) $
  |~ foldProduct (.*.) (map other.Var.H (x ::: xs ++ (y :: ys)))
  ~~ foldProduct (.*.) (other.Var.H x ::: (map other.Var.H xs) ++ map other.Var.H (y :: ys)) 
          .=. (cong (foldProduct (.*.)) (cong (other.Var.H x :::) (mapAppend _ _ _)))
  ~~ foldProduct (.*.) (other.Var.H x ::: (map other.Var.H xs)) .*. foldProduct (.*.) (map other.Var.H (y ::: ys)) 
          ... (foldProductSplit _ _ _ _)
    
public export
mapAppendl : (xs, ys : List1 a) -> (f : a -> b) ->
  map f (xs ++ ys) = appendl (map f xs) (forget (map f ys))
mapAppendl (x ::: xs) (y ::: ys) f = cong (f x :::) (mapAppend f _ _)
  
public export
ExtenderPreservesPrependVars : (sg : Semigroup) -> (s : Setoid) ->
  (other : Extension sg s) -> (xs : List1 (U s)) -> (js : FrexCarrier sg s) ->
  let (.*.) = other.Model.sem Product in
  other.Model.rel
    (ExtenderFunction sg s other (MkVars $ prependVars {sg} xs js))
    (foldProduct (other.Model.sem Product) (map (other.Var.H) xs) .*. ExtenderFunction sg s other js)
ExtenderPreservesPrependVars sg s other xs (MkVars (OneVars ys)) = 
  ExtenderPreservesConcat sg s other xs ys
ExtenderPreservesPrependVars sg s other xs (MkVars (ConsVars ys is)) =
  let (.*.) : U (cast other.Model) -> U (cast other.Model) -> U (cast other.Model)
      (.*.) = other.Model.sem Product
      (:*:) : Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1)
      (:*:) = call {sig = Signature} Product
      h : U (FrexSemigroup sg s) -> U other.Model
      h = ExtenderFunction sg s other
  in
  CalcWith (cast other.Model) $
  |~ foldProduct (.*.) (map other.Var.H (xs ++ ys)) .*. h (MkConc is)
  ~~ foldProduct (.*.) (appendl (map other.Var.H xs) (forget (map other.Var.H ys))) .*. h (MkConc is) 
          .=. (cong (.*. h (MkConc is)) (cong (foldProduct (.*.)) (mapAppendl _ _ _)))
  ~~ (foldProduct (.*.) (map other.Var.H xs) .*. foldProduct (.*.) (map other.Var.H ys)) .*. h (MkConc is) 
          ... (other.Model.cong 1 (Dyn 0 :*: Sta _) [_] [_] [foldProductSplit1 _ _])
  ~~ foldProduct (.*.) (map other.Var.H xs) .*. (foldProduct (.*.) (map other.Var.H ys) .*. h (MkConc is)) 
          ..< (other.Model.validate Associativity [_, _, _])
ExtenderPreservesPrependVars sg s other xs (MkConc _) =
  other.Model.equivalence.reflexive _

public export
ExtenderPreservesPrependConc : (sg : Semigroup) -> (s : Setoid) ->
  (other : Extension sg s) -> (i : U sg) -> (js : FrexCarrier sg s) ->
  let (.*.) = other.Model.sem Product in
  other.Model.rel
    (ExtenderFunction sg s other (MkConc $ prependConc sg i js))
    (other.Embed.H.H i .*. ExtenderFunction sg s other js)
ExtenderPreservesPrependConc sg s other i (MkVars _) = 
  other.Model.equivalence.reflexive _
ExtenderPreservesPrependConc sg s other i (MkConc (OneConc x)) = 
  other.Embed.preserves Prod [_, _]
ExtenderPreservesPrependConc sg s other i (MkConc (ConsConc x is)) = 
  let (.*.) : U other.Model -> U other.Model -> U other.Model
      (.*.) = other.Model.sem Product
      (:*:) : Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1)
      (:*:) = call {sig = Signature} Product
      h : U (FrexSemigroup sg s) -> U other.Model
      h = ExtenderFunction sg s other
  in
  CalcWith (cast other.Model) $
  |~ other.Embed.H.H (sg.sem Product i x) .*. h (MkVars is)
  ~~ (other.Embed.H.H i .*. other.Embed.H.H x) .*. h (MkVars is) 
        ... (other.Model.cong 1 (Dyn 0 :*: Sta _) [_] [_] 
            [other.Embed.preserves Prod [i, x]])
  ~~ other.Embed.H.H i .*. (other.Embed.H.H x .*. h (MkVars is)) 
        ..< (other.Model.validate Associativity [_, _, _])

public export
ExtenderPreservesProd : (sg : Semigroup) -> (s : Setoid) ->
  (other : Extension sg s) ->
  (is,js : FrexCarrier sg s) ->
  let (.*.) = other.Model.sem Product
      (:*:) = (FrexSemigroup sg s).sem Product
      h : U (FrexSemigroup sg s) -> U other.Model
      h = ExtenderFunction sg s other
  in other.Model.rel
    (h (is :*: js) )
    (h is .*. h js)
ExtenderPreservesProd sg s other (MkVars (OneVars xs)) js =
  ExtenderPreservesPrependVars sg s other xs js
ExtenderPreservesProd sg s other (MkVars (ConsVars xs is)) js = 
  let (.*.) : U other.Model -> U other.Model -> U other.Model
      (.*.) = other.Model.sem Product
      (:*:) : Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1)
      (:*:) = call {sig = Signature} Product
      h : U (FrexSemigroup sg s) -> U other.Model
      h = ExtenderFunction sg s other
  in
  CalcWith (cast other.Model) $
  |~ h (MkVars $ prependVars xs $ MkConc is ++ js)
  ~~ (foldProduct (.*.) (map (other.Var.H) xs)) .*. h (MkConc is ++ js) ... (ExtenderPreservesPrependVars _ _ _ _ _)
  ~~ (foldProduct (.*.) (map (other.Var.H) xs)) .*. (h (MkConc is) .*. h js) 
          ... (other.Model.cong 1 (Sta _ :*: Dyn 0) [_] [_] [ExtenderPreservesProd _ _ _ (assert_smaller (MkVars (ConsVars xs is)) (MkConc is)) _])
  ~~ ((foldProduct (.*.) (map (other.Var.H) xs)) .*. h (MkConc is)) .*. h js ... (other.Model.validate Associativity [_, _, _])
ExtenderPreservesProd sg s other (MkConc (OneConc x)) js = 
  ExtenderPreservesPrependConc sg s other x js
ExtenderPreservesProd sg s other (MkConc (ConsConc x is)) js = 
  let (.*.) : U other.Model -> U other.Model -> U other.Model
      (.*.) = other.Model.sem Product
      (:*:) : Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1) -> 
              Term Signature (U other.Model `Either` Fin 1)
      (:*:) = call {sig = Signature} Product
      h : U (FrexSemigroup sg s) -> U other.Model
      h = ExtenderFunction sg s other
  in
  CalcWith (cast other.Model) $
  |~ h (MkConc $ prependConc sg x $ MkVars is ++ js)
  ~~ other.Embed.H.H x .*. h (MkVars is ++ js) ... (ExtenderPreservesPrependConc _ _ _ _ _)
  ~~ other.Embed.H.H x .*. (h (MkVars is) .*. h js) 
          ... (other.Model.cong 1 (Sta _ :*: Dyn 0) [_] [_] [ExtenderPreservesProd _ _ _ (assert_smaller (MkConc (ConsConc x is)) (MkVars is)) _])
  ~~ (other.Embed.H.H x .*. h (MkVars is)) .*. h js ... (other.Model.validate Associativity [_, _, _])

public export
ExtenderIsHomomorphism : (sg : Semigroup) -> (s : Setoid) ->
  ExtenderIsHomomorphism (Extension sg s) (ExtenderFunction sg s)
ExtenderIsHomomorphism a s other (MkOp Product) [is,js] =
  ExtenderPreservesProd a s other is js

public export
lemma1 : (sg : Semigroup) -> (s : Setoid) -> (other : Extension sg s) ->
  (xs, ys : List1 (U s)) -> (prf : s.List1Equality xs ys) ->
  other.Model.rel
    (foldProduct (other.Model.sem Product) (map (other.Var.H) xs))
    (foldProduct (other.Model.sem Product) (map (other.Var.H) ys))
lemma1 sg s other xs ys prf =
  foldProductHomomorphism {a = cast other.Model} (other.Model.sem Product) _ _
  (List1MapFunctionHomomorphism (other.Var) xs ys prf) $
  \x,y,z,w, x_eq_y, z_eq_w =>
  other.Model.Algebra.congruence (MkOp Product) [x, z] [y, w] 
    (\case 0 => x_eq_y; 1 => z_eq_w)

public export
ExtenderIsSetoidHomomorphism : (sg : Semigroup) -> (s : Setoid) -> (other : Extension sg s) ->
  (is,js : FrexCarrier sg s) ->
  (prf : (FrexSemigroup sg s).rel is js) ->
  other.Model.rel
    (ExtenderFunction sg s other is)
    (ExtenderFunction sg s other js)
ExtenderIsSetoidHomomorphism sg s other (MkVars (OneVars xs)) (MkVars (OneVars ys))
  (EqVars $ EqOneVars xs_eq_ys) = lemma1 sg s other xs ys xs_eq_ys
ExtenderIsSetoidHomomorphism sg s other (MkVars (ConsVars xs is)) (MkVars (ConsVars ys js))
  (EqVars $ EqConsVars xs_eq_ys is_eq_js) = 
  let (.*.) : Term Signature (U other.Model `Either` Fin 2) -> 
              Term Signature (U other.Model `Either` Fin 2) -> 
              Term Signature (U other.Model `Either` Fin 2)
      (.*.) = call {sig = Signature} Product 
  in 
  other.Model.cong 2 (Dyn 0 .*. Dyn 1) [_,_] [_,_] 
  [ lemma1 sg s other xs ys xs_eq_ys
  , ExtenderIsSetoidHomomorphism sg s other 
    (assert_smaller (MkVars (ConsVars xs is)) (MkConc is)) 
    (assert_smaller (MkVars (ConsVars ys js)) (MkConc js)) 
    (EqConc is_eq_js)
  ]
ExtenderIsSetoidHomomorphism sg s other (MkConc (OneConc x)) (MkConc (OneConc y)) (EqConc $ EqOneConc x_eq_y) = 
  other.Embed.H.homomorphic x y x_eq_y
ExtenderIsSetoidHomomorphism sg s other (MkConc (ConsConc x is)) (MkConc (ConsConc y js)) (EqConc $ EqConsConc x_eq_y is_eq_js) = 
  let (.*.) : Term Signature (U other.Model `Either` Fin 2) -> 
              Term Signature (U other.Model `Either` Fin 2) -> 
              Term Signature (U other.Model `Either` Fin 2)
      (.*.) = call {sig = Signature} Product 
  in 
  other.Model.cong 2 (Dyn 0 .*. Dyn 1) [_,_] [_,_] 
  [ other.Embed.H.homomorphic x y x_eq_y
  , ExtenderIsSetoidHomomorphism sg s other 
    (assert_smaller (MkConc (ConsConc x is)) (MkVars is)) 
    (assert_smaller (MkConc (ConsConc y js)) (MkVars js)) 
    (EqVars is_eq_js)
  ]
ExtenderIsSetoidHomomorphism _ _ _ (MkVars (OneVars _)) (MkVars (ConsVars _ _)) prf = absurd prf
ExtenderIsSetoidHomomorphism _ _ _ (MkVars (ConsVars _ _)) (MkVars (OneVars _)) prf = absurd prf
ExtenderIsSetoidHomomorphism _ _ _ (MkConc (OneConc _)) (MkConc (ConsConc _ _)) prf = absurd prf
ExtenderIsSetoidHomomorphism _ _ _ (MkConc (ConsConc _ _)) (MkConc (OneConc _)) prf = absurd prf

public export
ExtenderHomomorphism : (sg : Semigroup) -> (s : Setoid) -> Frex.Frex.ExtenderHomomorphism (Extension sg s)
ExtenderHomomorphism sg s other = MkSetoidHomomorphism
  { H = MkSetoidHomomorphism
      { H           = ExtenderFunction sg s other
      , homomorphic = ExtenderIsSetoidHomomorphism sg s other
      }
  , preserves = ExtenderIsHomomorphism sg s other
  }

public export
ExtenderPreservesEmbedding : (sg : Semigroup) -> (s : Setoid) ->
  ExtenderPreservesEmbedding (Extension sg s) (ExtenderHomomorphism sg s)
ExtenderPreservesEmbedding sg s other x = other.Model.equivalence.reflexive _

public export
ExtenderPreservesVars : (sg : Semigroup) -> (s : Setoid) ->
  ExtenderPreservesVars (Extension sg s) (ExtenderHomomorphism sg s)
ExtenderPreservesVars sg s other x = other.Model.equivalence.reflexive _

public export
Extender : (sg : Semigroup) -> (s : Setoid) -> Extender (Extension sg s)
Extender sg s other = MkExtensionMorphism
  { H             = ExtenderHomomorphism       sg s other
  , PreserveEmbed = ExtenderPreservesEmbedding sg s other
  , PreserveVar   = ExtenderPreservesVars      sg s other
  }

public export
Uniqueness : (a : Semigroup) -> (s : Setoid) -> Uniqueness (Extension a s)
Uniqueness a s other extend1 extend2 is = 
  let frex : Extension a s
      frex = Extension a s
      lemma1 : (extend : frex ~> other) -> (is : U frex.Model) ->
        other.Model.rel
          (extend.H.H.H is)
          (other.Model.Sem (reify a s is) (extend.H.H.H . (either a.sta a.dyn)))
      lemma1 extend is = CalcWith (cast other.Model) $
        |~ extend.H.H.H is
        ~~ extend.H.H.H (frex.Sem (reify a s is) (either a.sta a.dyn))
             ..<( extend.H.H.homomorphic _ _ $ normalForm a s is )
        ~~ other.Model.Sem (reify a s is) (extend.H.H.H . (either a.sta a.dyn))
             ...(homoPreservesSem extend.H _ _)
      lemma2 : ((cast a `Either` s) ~~> cast other.Model).equivalence.relation
                  (extend1.H.H . (either frex.Embed.H frex.Var))
                  (extend2.H.H . (either frex.Embed.H frex.Var))
      lemma2 (Left  i) = CalcWith (cast other.Model) $
        |~ extend1.H.H.H (frex.Embed.H.H i)
        ~~ other.Embed.H.H i                 ...(extend1.PreserveEmbed i)
        ~~ extend2.H.H.H (frex.Embed.H.H i)  ..<(extend2.PreserveEmbed i)
      lemma2 (Right x) = CalcWith (cast other.Model) $
        |~ extend1.H.H.H (frex.Var.H x)
        ~~ other.Var.H x                ...(extend1.PreserveVar x)
        ~~ extend2.H.H.H (frex.Var.H x) ..<(extend2.PreserveVar x)
  in CalcWith (cast other.Model) $
  |~ extend1.H.H.H is
  ~~ other.Model.Sem (reify a s is) (extend1.H.H.H . (either a.sta a.dyn))
       ...(lemma1 extend1 is)
  ~~ other.Model.Sem (reify a s is) (extend2.H.H.H . (either a.sta a.dyn))
       ...((eval (reify a s is)).homomorphic
             (extend1.H.H . (either frex.Embed.H frex.Var))
             (extend2.H.H . (either frex.Embed.H frex.Var))
             $ lemma2)
  ~~ extend2.H.H.H is ..<(lemma1 extend2 is)

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