||| This module lists some basic properties that hold in every group
module Frexlet.Group.Properties

import Frex

import Frexlet.Group.Theory
import Frexlet.Group.Notation

%hide Monoid.Theory.Signature

public export
inverseUniqueLeft : (a : Group) ->
  (x, y : U a) ->
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
  in
  a.rel (x .*. y) I1 ->
  a.rel x (a.inv y)
inverseUniqueLeft a x y eq =
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
      notation' : Multiplicative1 (Term Signature (Fin 1))
      notation' = notationSyntax
  in
  CalcWith (cast a) $
  |~ x
  ~~ x .*. I1                ..< (a.validate (Mon RgtNeutrality) [_])
  ~~ x .*. (y .*. a.inv y)   ..< (a.cong 1 (Sta _ .*. Dyn 0) [_] [_] [a.validate RgtInverse [_]])
  ~~ (x .*. y) .*. a.inv y   ... (a.validate (Mon Associativity) [_, _, _])
  ~~ I1 .*. a.inv y          ... (a.cong 1 (Dyn 0 .*. Sta _) [_] [_] [eq])
  ~~ a.inv y                 ... (a.validate (Mon LftNeutrality) [_])


public export
inverseUniqueRight : (a : Group) ->
  (x, y : U a) ->
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
  in
  a.rel (x .*. y) I1 ->
  a.rel y (a.inv x)
inverseUniqueRight a x y eq =
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
      notation' : Multiplicative1 (Term Signature (Fin 1))
      notation' = notationSyntax
  in
  CalcWith (cast a) $
  |~ y
  ~~ I1 .*. y                ..< (a.validate (Mon LftNeutrality) [_])
  ~~ (a.inv x .*. x) .*. y   ..< (a.cong 1 (Dyn 0 .*. Sta _) [_] [_] [a.validate LftInverse [_]])
  ~~ a.inv x .*. (x .*. y)   ..< (a.validate (Mon Associativity) [_, _, _])
  ~~ a.inv x .*. I1          ... (a.cong 1 (Sta _ .*. Dyn 0) [_] [_] [eq])
  ~~ a.inv x                 ... (a.validate (Mon RgtNeutrality) [_])


public export
inverseInvolutive : (a : Group) -> (x : U a) ->
  a.rel x (a.inv $ a.inv x)
inverseInvolutive a x = 
  inverseUniqueLeft a x (a.inv x) $ 
  a.validate RgtInverse [_]

public export
inverseProduct : (a : Group) ->
  (x, y : U a) ->
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
  in
  a.rel (a.inv $ x .*. y) (a.inv y .*. a.inv x)
inverseProduct a x y =
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
      notation' : Multiplicative1 (Term Signature (Fin 1))
      notation' = notationSyntax
  in
  a.equivalence.symmetric _ _ $
  inverseUniqueRight a _ _ $
  CalcWith (cast a) $
  |~ (x .*. y) .*. (a.inv y .*. a.inv x)
  ~~ x .*. (y .*. (a.inv y .*. a.inv x)) 
                    ..< (a.validate (Mon Associativity) [_, _, _])
  ~~ x .*. ((y .*. a.inv y) .*. a.inv x) 
                    ... (a.cong 1 (Sta _ .*. Dyn 0) [_] [_] [a.validate (Mon Associativity) [_, _, _]])
  ~~ x .*. (I1 .*. a.inv x) 
                    ... (a.cong 1 (Sta _ .*. (Dyn 0 .*. Sta _)) [_] [_] [a.validate RgtInverse [_]])
  ~~ x .*. a.inv x  ... (a.cong 1 (Sta _ .*. Dyn 0) [_] [_] [a.validate (Mon LftNeutrality) [_]])
  ~~ I1             ... (a.validate RgtInverse [_])


public export
inverseNeutral : (a : Group) ->
  let %hint
      notation : Multiplicative1 (U a)
      notation = a.Multiplicative1
  in
  a.rel (a.inv I1) I1
inverseNeutral a = 
  a.equivalence.symmetric _ _ $
  inverseUniqueLeft a _ _ $
  a.validate (Mon LftNeutrality) [_]
