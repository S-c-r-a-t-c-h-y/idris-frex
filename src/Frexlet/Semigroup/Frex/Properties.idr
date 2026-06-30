||| Properties of the semigroup frexlet and its operations
module Frexlet.Semigroup.Frex.Properties

import Frex

import Frexlet.Semigroup.Theory
import Frexlet.Semigroup.Frex.Structure

import Data.List1
import Data.List1.Properties

import Data.Setoid.List1

%default total


------------------------- prependVars lemmas -------------------------
public export
List1appendAssociative : (s : Setoid) -> (xs, ys, zs : List1 (U s)) ->
  s.List1Equality (xs ++ (ys ++ zs)) ((xs ++ ys) ++ zs)
List1appendAssociative s xs ys zs =
  s.List1EqualityReflexiveEqual _ _ (appendAssociative xs ys zs)

public export
prependVarsCong : {sg : Semigroup} -> {pen : Setoid} ->
  (pref : List1 $ U pen) -> (y, z : Mon (U pen) (U sg)) -> MonEquality pen.List1Equality sg.equivalence.relation y z ->
  MonNEEquality pen.List1Equality sg.equivalence.relation (prependVars {sg} pref y) (prependVars {sg} pref z)

prependVarsCong {sg} {pen} pref (MkVars (OneVars xs)) (MkVars (OneVars ys)) 
  (EqVars $ EqOneVars xs_eq_ys) = 
  EqOneVars $ appendCongruence pref xs pref ys (pen.List1EqualityReflexive pref) xs_eq_ys
prependVarsCong {sg} {pen} pref (MkVars (ConsVars xs1 is1)) (MkVars (ConsVars xs2 is2)) 
  (EqVars $ EqConsVars xs1_eq_xs2 is1_eq_is2) = 
  EqConsVars (appendCongruence pref xs1 pref xs2 (pen.List1EqualityReflexive pref) xs1_eq_xs2) is1_eq_is2
prependVarsCong {sg} {pen} pref (MkConc (OneConc y)) (MkConc (OneConc z)) 
  (EqConc $ EqOneConc y_eq_z) = 
  EqConsVars (pen.List1EqualityReflexive pref) (EqOneConc y_eq_z)
prependVarsCong {sg} {pen} pref (MkConc (ConsConc y is1)) (MkConc (ConsConc z is2)) 
  (EqConc $ EqConsConc y_eq_z is1_eq_is2) = 
  EqConsVars (pen.List1EqualityReflexive pref) (EqConsConc y_eq_z is1_eq_is2)
prependVarsCong _ (MkVars (OneVars _)) (MkVars (ConsVars _ _)) (EqVars _) impossible
prependVarsCong _ (MkVars (ConsVars _ _)) (MkVars (OneVars _)) (EqVars _) impossible
prependVarsCong _ (MkConc (OneConc _)) (MkConc (ConsConc _ _)) (EqConc _) impossible
prependVarsCong _ (MkConc (ConsConc _ _)) (MkConc (OneConc _)) (EqConc _) impossible

public export
prependVarsAssociative2 : (sg : Semigroup) -> (x : Setoid) -> (xs, ys : List1 (U x)) ->
  (ks : FrexCarrier sg x) ->
  MonNEEquality (x.List1Equality) sg.equivalence.relation 
    (prependVars {sg} xs (MkVars (prependVars {sg} ys ks))) 
    (prependVars {sg} (xs ++ ys) ks)
prependVarsAssociative2 sg x xs ys (MkVars (OneVars zs)) = 
  EqOneVars $ List1appendAssociative x _ _ _
prependVarsAssociative2 sg x xs ys (MkVars (ConsVars zs is)) = 
  EqConsVars (List1appendAssociative x _ _ _) $ MonNEReflexive x (cast sg) _
prependVarsAssociative2 sg x _ _ (MkConc _) = 
  EqConsVars (x.List1EqualityReflexive _) $ MonNEReflexive x (cast sg) _

public export
prependVarsAssociative : (sg : Semigroup) -> (x : Setoid) -> (xs : List1 (U x)) ->
  (js, ks : FrexCarrier sg x) ->
  MonEquality (x.List1Equality) sg.equivalence.relation 
  (MkVars (prependVars {sg} xs ((++) {sg} js ks))) 
  ((++) {sg} (MkVars (prependVars {sg} xs js)) ks)
prependVarsAssociative sg x xs (MkVars (OneVars ys)) ks = 
  EqVars $ prependVarsAssociative2 sg x xs ys ks
prependVarsAssociative sg x xs (MkVars (ConsVars ys is)) ks = 
  EqVars $ prependVarsAssociative2 sg x xs ys ((MkConc is) ++ ks)
prependVarsAssociative sg x xs (MkConc (OneConc y)) ks = 
  MonReflexive x (cast sg) _
prependVarsAssociative sg x xs (MkConc (ConsConc y is)) ks = 
  MonReflexive x (cast sg) _

------------------------- prependConc lemmas -------------------------
public export
prependConcCong : (sg : Semigroup) -> (i : U sg) -> (y, z : Mon (U pen) (U sg)) ->
  MonEquality pen.List1Equality sg.equivalence.relation y z ->
  MonNEEquality pen.List1Equality sg.equivalence.relation (prependConc sg i y) (prependConc sg i z)

prependConcCong sg i (MkVars (OneVars xs)) (MkVars (OneVars ys)) (EqVars $ EqOneVars xs_eq_ys) = 
  EqConsConc (sg.equivalence.reflexive i) $ EqOneVars xs_eq_ys
prependConcCong sg i (MkVars (ConsVars xs1 is1)) (MkVars (ConsVars xs2 is2)) (EqVars $ EqConsVars xs1_eq_xs2 is1_eq_is2) = 
  EqConsConc (sg.equivalence.reflexive i) (EqConsVars xs1_eq_xs2 is1_eq_is2)
prependConcCong sg i (MkConc (OneConc y)) (MkConc (OneConc z)) (EqConc $ EqOneConc y_eq_z) = 
  EqOneConc $ sg.cong 2 (call {sig = Signature} Product (Dyn 0) (Dyn 1)) [_,_] [_,_] [sg.equivalence.reflexive i, y_eq_z]
prependConcCong sg i (MkConc (ConsConc y is1)) (MkConc (ConsConc z is2)) (EqConc $ EqConsConc y_eq_z is1_eq_is2) = 
  EqConsConc (sg.cong 2 (call {sig = Signature} Product (Dyn 0) (Dyn 1)) [_,_] [_,_] [sg.equivalence.reflexive i, y_eq_z]) is1_eq_is2
prependConcCong _ _ (MkVars (OneVars _)) (MkVars (ConsVars _ _)) (EqVars _) impossible
prependConcCong _ _ (MkVars (ConsVars _ _)) (MkVars (OneVars _)) (EqVars _) impossible
prependConcCong _ _ (MkConc (OneConc _)) (MkConc (ConsConc _ _)) (EqConc _) impossible
prependConcCong _ _ (MkConc (ConsConc _ _)) (MkConc (OneConc _)) (EqConc _) impossible

public export
prependConcAssociative2 : (sg : Semigroup) -> (x : Setoid) -> (i, j : U sg) ->
  (ks : FrexCarrier sg x) ->
  MonNEEquality (x.List1Equality) sg.equivalence.relation 
    (prependConc sg i (MkConc $ prependConc sg j ks)) 
    (prependConc sg (sg.sem Product i j) ks)
prependConcAssociative2 sg x i j (MkConc (OneConc k)) = 
  EqOneConc $ sg.validate Associativity [_, _, _]
prependConcAssociative2 sg x i j (MkConc (ConsConc k is)) = 
  EqConsConc (sg.validate Associativity [_, _, _]) (MonNEReflexive x (cast sg) _)
prependConcAssociative2 sg x _ _ (MkVars _) = 
  MonNEReflexive x (cast sg) _

public export
prependConcAssociative : (sg : Semigroup) -> (x : Setoid) -> (i : U sg) ->
  (js, ks : FrexCarrier sg x) ->
  MonEquality (x.List1Equality) sg.equivalence.relation 
  (MkConc (prependConc sg i ((++) {sg} js ks))) 
  ((++) {sg} (MkConc (prependConc sg i js)) ks)
prependConcAssociative sg x i (MkVars ys) ks = 
  MonReflexive x (cast sg) _
prependConcAssociative sg x i (MkConc (OneConc y)) ks = 
  EqConc $ prependConcAssociative2 sg x i y ks
prependConcAssociative sg x i (MkConc (ConsConc y is)) ks = 
  EqConc $ prependConcAssociative2 sg x i y ((MkVars is) ++ ks)

------------------------- appendAssociative -------------------------
public export
appendAssociative : (sg : Semigroup) -> (x : Setoid) -> (is, js, ks : FrexCarrier sg x) ->
  (FrexSetoid sg x).equivalence.relation
    ((FrexStructure sg x).sem Product is ((FrexStructure sg x).sem Product js ks))
    ((FrexStructure sg x).sem Product ((FrexStructure sg x).sem Product is js) ks)
appendAssociative sg x (MkVars (OneVars xs)) js ks = prependVarsAssociative sg x xs js ks
appendAssociative sg x (MkVars (ConsVars xs is)) js ks =
  MonTransitive x (cast sg)
  (MkVars $ prependVars {sg} xs (MkConc is ++ (js ++ ks)))
  (MkVars $ prependVars {sg} xs ((MkConc is ++ js) ++ ks))
  (MkVars (prependVars {sg} xs (MkConc is ++ js)) ++ ks)
  (EqVars $ prependVarsCong {sg} xs (MkConc is ++ (js ++ ks)) ((MkConc is ++ js) ++ ks) 
    (appendAssociative sg x (assert_smaller (MkVars (ConsVars xs is)) (MkConc is)) js ks))
  (prependVarsAssociative sg x xs (MkConc is ++ js) ks)
appendAssociative sg x (MkConc (OneConc y)) js ks = prependConcAssociative sg x y js ks
appendAssociative sg x (MkConc (ConsConc y is)) js ks = 
  MonTransitive x (cast sg)
  (MkConc $ prependConc sg y (MkVars is ++ (js ++ ks)))
  (MkConc $ prependConc sg y ((MkVars is ++ js) ++ ks))
  (MkConc (prependConc sg y (MkVars is ++ js)) ++ ks)
  (EqConc $ prependConcCong sg y (MkVars is ++ (js ++ ks)) ((MkVars is ++ js) ++ ks) 
    (appendAssociative sg x (assert_smaller (MkConc (ConsConc y is)) (MkVars is)) js ks))
  (prependConcAssociative sg x y (MkVars is ++ js) ks)

public export 
FrexValidatesAxioms : (sg : Semigroup) -> (x : Setoid) -> Validates SemigroupTheory (FrexStructure sg x)
FrexValidatesAxioms sg x Associativity env = appendAssociative sg x (env 0) (env 1) (env 2)

public export
FrexSemigroup : (sg : Semigroup) -> (x : Setoid) -> Semigroup
FrexSemigroup sg x = MkModel
  { Algebra = FrexStructure sg x
  , Validate = FrexValidatesAxioms sg x
  }