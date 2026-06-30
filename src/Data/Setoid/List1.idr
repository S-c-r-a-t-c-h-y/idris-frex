||| Setoid of lists over a setoid and associated definitions
module Data.Setoid.List1

import Data.List1
import Data.Setoid.Definition
import Data.Setoid.List

%default total

namespace Relation
  public export
  data (.List1Equality) : (a : Setoid) -> Rel (List1 $ U a) where
    (:::) : (hdEq : a.equivalence.relation x y) -> (tlEq : a.ListEquality xs ys) ->
          a.List1Equality (x ::: xs) (y ::: ys)
          
public export
(.List1EqualityReflexive) : (a : Setoid) -> (xs : List1 $ U a) -> a.List1Equality xs xs
a.List1EqualityReflexive (x ::: xs) = a.equivalence.reflexive x ::: a.ListEqualityReflexive xs

public export
(.List1EqualityReflexiveEqual) : (a : Setoid) -> (xs, ys : List1 $ U a) ->
  (prf : xs = ys) -> a.List1Equality xs ys
a.List1EqualityReflexiveEqual xs xs Refl = a.List1EqualityReflexive xs

public export
(.List1EqualitySymmetric) : (a : Setoid) -> (xs,ys : List1 $ U a) -> (prf : a.List1Equality xs ys) ->
  a.List1Equality ys xs
a.List1EqualitySymmetric (x ::: xs) (y ::: ys) (hdEq ::: tlEq)
  = a.equivalence.symmetric x y hdEq ::: a.ListEqualitySymmetric xs ys tlEq

public export
(.List1EqualityTransitive) : (a : Setoid) -> (xs,ys,zs : List1 $ U a) ->
  (prf1 : a.List1Equality xs ys) -> (prf2 : a.List1Equality ys zs) ->
  a.List1Equality xs zs
a.List1EqualityTransitive (x ::: xs) (y ::: ys) (z ::: zs) (hdEq1 ::: tlEq1) (hdEq2 ::: tlEq2)
  = a.equivalence.transitive x  y  z  hdEq1 hdEq2 :::
    a.ListEqualityTransitive xs ys zs tlEq1 tlEq2

public export
List1Setoid : (a : Setoid) -> Setoid
List1Setoid a = MkSetoid (List1 $ U a)
  $ MkEquivalence
  { relation   = a.List1Equality
  , reflexive  = a.List1EqualityReflexive
  , symmetric  = a.List1EqualitySymmetric
  , transitive = a.List1EqualityTransitive
  }

public export
List1MapFunctionHomomorphism : (f : a ~> b) ->
  SetoidHomomorphism (List1Setoid a) (List1Setoid b) (map f.H)
List1MapFunctionHomomorphism f (x ::: xs) (y ::: ys) (hdEq ::: tlEq) =
  f.homomorphic x y hdEq ::: ListMapFunctionHomomorphism f xs ys tlEq

public export
List1MapHomomorphism : (f : a ~> b) -> (List1Setoid a ~> List1Setoid b)
List1MapHomomorphism f = MkSetoidHomomorphism (map f.H) (List1MapFunctionHomomorphism f)

public export
List1MapIsHomomorphism : SetoidHomomorphism (a ~~> b) (List1Setoid a ~~> List1Setoid b)
  List1MapHomomorphism
List1MapIsHomomorphism f g f_eq_g (x ::: xs) = f_eq_g x ::: ListMapIsHomomorphism f g f_eq_g xs

public export
List1Map : {0 a, b : Setoid} -> (a ~~> b) ~> (List1Setoid a ~~> List1Setoid b)
List1Map = MkSetoidHomomorphism
  { H           = List1MapHomomorphism
  , homomorphic = List1MapIsHomomorphism
  }

-- public export
-- reverseHomomorphic : {a : Setoid} -> (x, y : List1 (U a)) ->
--   (a.List1Equality x y) -> a.List1Equality (reverse x) (reverse y)
-- reverseHomomorphic x y prf = roh [] [] x y (a.ListEqualityReflexive _) prf
--   where roh  : (ws, xs, ys, zs : List (U a)) -> a.List1Equality ws xs -> a.List1Equality ys zs ->
--                a.List1Equality (reverseOnto ws ys) (reverseOnto xs zs)
--         roh ws xs   []      []    wx     []       = wx
--         roh ws xs (y::ys) (z::zs) wx (yzh :: yzt) = roh (y::ws) (z::xs) ys zs (yzh :: wx) yzt

public export
appendCongruence : {a : Setoid} -> (x1, x2, y1, y2 : List1 (U a)) ->
  a.List1Equality x1 y1 -> a.List1Equality x2 y2 -> a.List1Equality (x1 ++ x2) (y1 ++ y2)
appendCongruence (x:::xs) (u:::us) (y:::ys) (v:::vs) (ph:::pt) (qh:::qt) =
  ph ::: List.appendCongruence xs (forget (u ::: us)) ys (forget (v ::: vs)) pt (qh :: qt)
