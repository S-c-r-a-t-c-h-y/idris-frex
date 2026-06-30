module Frexlet.Group.Free.Structure

import Frex

import Frexlet.Group.Theory

import Data.Setoid
import Data.Setoid.List

import Decidable.Equality
import Data.List

import Notation.Action

%default total

public export
data Letter : Nat -> Type where
  Pos : Fin n -> Letter n
  Neg : Fin n -> Letter n

export
Uninhabited (Pos n = Neg m) where uninhabited eq impossible 
export
Uninhabited (Neg n = Pos m) where uninhabited eq impossible 

public export
LetterSetoid : (n : Nat) -> Setoid
LetterSetoid n = cast $ Letter n

public export
DecEq (Letter n) where
  decEq (Pos x) (Pos y) with (decEq x y)
    _ | Yes prf = Yes $ cong Pos prf
    _ | No nprf = No (\ Refl => nprf Refl)
  decEq (Pos x) (Neg y) = No absurd
  decEq (Neg x) (Pos y) = No absurd
  decEq (Neg x) (Neg y) with (decEq x y)
    _ | Yes prf = Yes $ cong Neg prf
    _ | No nprf = No (\ Refl => nprf Refl)

public export
invLetter : Letter n -> Letter n
invLetter (Pos i) = Neg i
invLetter (Neg i) = Pos i

public export
invLetterHomomorphism : {n : Nat} -> LetterSetoid n ~> LetterSetoid n
invLetterHomomorphism = mate invLetter

public export
invLetterInvolutive : (x : Letter n) -> invLetter (invLetter x) = x
invLetterInvolutive (Pos x) = Refl
invLetterInvolutive (Neg x) = Refl

public export
invInjective : (l1, l2 : Letter n) ->
  (invLetter l1 = invLetter l2) -> l1 = l2
invInjective (Pos x) (Pos x) Refl = Refl
invInjective (Neg x) (Neg x) Refl = Refl

public export
notInvSwap : Not (y = invLetter x) -> Not (x = invLetter y)
notInvSwap notYX xEqInvY =
  notYX (sym $ rewrite sym $ invLetterInvolutive y in cong invLetter xEqInvY)

public export
notInv : Not (y = invLetter x) -> Not (invLetter y = x)
notInv notYX invYEqX =
  notYX (rewrite sym $ invLetterInvolutive y in cong invLetter invYEqX)

public export
RawWord : (n : Nat) -> Type
RawWord n = List (Letter n)

public export
RawWordSetoid : (n : Nat) -> Setoid
RawWordSetoid n = ListSetoid (LetterSetoid n)

public export
data Reduced : RawWord n -> Type where
  RNil  : Reduced []
  ROne  : (x : Letter n) -> Reduced [x]
  RCons : {x, y : Letter n} ->
          Not (y = invLetter x) ->
          Reduced (y :: zs) ->
          Reduced (x :: y :: zs)

public export
record FreeCarrier (n : Nat) where
  constructor MkFreeCarrier
  word    : RawWord n
  reduced : Reduced word

public export
tailReduced : Reduced (x :: xs) -> Reduced xs
tailReduced (ROne _) = RNil
tailReduced (RCons _ p) = p

public export
reduceFront : Letter n -> FreeCarrier n -> FreeCarrier n
reduceFront x (MkFreeCarrier [] RNil) = MkFreeCarrier [x] (ROne x)
reduceFront x (MkFreeCarrier (y :: ys) p) with (decEq y (invLetter x))
  _ | (Yes _)     = MkFreeCarrier ys (tailReduced p)
  _ | (No notInv) = MkFreeCarrier (x :: y :: ys) (RCons notInv p)

public export
reduce : RawWord n -> FreeCarrier n
reduce [] = MkFreeCarrier [] RNil
reduce (x :: xs) = reduceFront x (reduce xs)


public export
reduceFrontStable :
  {x  : Letter n} ->
  {ys : RawWord n} ->
  (pxy : Reduced (x :: ys)) ->
  (py  : Reduced ys) ->
  (reduceFront x (MkFreeCarrier ys py)).word = x :: ys
reduceFrontStable {ys = []} (ROne x) RNil = Refl
reduceFrontStable {x} {ys = y :: zs} (RCons notInv pTail) py
  with (decEq y (invLetter x))
  _ | (Yes eq) = absurd (notInv eq)
  _ | (No neq) = Refl

public export
reduceReduced : (xs : RawWord n) -> (p : Reduced xs) -> (reduce xs).word = xs
reduceReduced [] RNil = Refl
reduceReduced (x :: xs) p =
  let ih : (reduce xs).word === xs
      ih = reduceReduced xs (tailReduced p)
      p' : Reduced (x :: (reduce xs).word)
      p' = rewrite ih in p
      front : (reduceFront x (reduce xs)).word = x :: (reduce xs).word
      front = believe_me $ reduceFrontStable p' (reduce xs).reduced -- FIXME: stupid inference issue
      rhs : x :: (reduce xs).word = x :: xs
      rhs = cong (x ::) ih
  in
  trans front rhs


public export
reduceFreeWord : (x : FreeCarrier n) -> (reduce x.word).word = x.word
reduceFreeWord (MkFreeCarrier word reduced) = reduceReduced word reduced

public export
mul : FreeCarrier n -> FreeCarrier n -> FreeCarrier n
mul u v = reduce (word u ++ word v)

public export
invWord : RawWord n -> RawWord n
invWord xs = reverse (map invLetter xs)

public export
mapInvReduced : (x : FreeCarrier n) -> Reduced (map Structure.invLetter x.word)
mapInvReduced (MkFreeCarrier [] _) = RNil
mapInvReduced (MkFreeCarrier (x :: []) _) = ROne _
mapInvReduced (MkFreeCarrier (x :: (y :: ys)) (RCons nprf red))
  with (decEq (invLetter y) (invLetter (invLetter x)))
  _ | Yes prf = 
      assert_total
      $ RCons (rewrite invLetterInvolutive x in notInv nprf) 
      $ mapInvReduced (MkFreeCarrier (y :: ys) red)
  _ | No contra = assert_total $ RCons contra $ mapInvReduced (MkFreeCarrier (y :: ys) red)

public export
snocReduced :
  {ys : List (Letter n)} ->
  {last, new : Letter n} ->
  Reduced (ys ++ [last]) ->
  Not (new = invLetter last) ->
  Reduced ((ys ++ [last]) ++ [new])
snocReduced {ys = []} {last} {new} (ROne _) notInv = RCons notInv (ROne new)
snocReduced {ys = z :: []} {last} {new} (RCons notInvHead (ROne _)) notInvLast =
  RCons notInvHead (RCons notInvLast (ROne new))
snocReduced {ys = z :: z' :: zs} {last} {new} (RCons notInvHead pTail) notInvLast =
  RCons notInvHead (snocReduced {ys = z' :: zs} {last} {new} pTail notInvLast)

public export
reverseCons : (x : a) -> (xs : List a) -> reverse (x :: xs) = reverse xs ++ [x]
reverseCons x xs = sym $ revAppend [x] _

public export
reverseReduced : {xs : RawWord n} -> Reduced xs -> Reduced (reverse xs)
reverseReduced {xs = []} RNil = RNil
reverseReduced {xs = [x]} (ROne x) = ROne x
reverseReduced {xs = x :: y :: zs} (RCons {x} {y} {zs} notInv pTail) =
  let ih : Reduced (reverse zs ++ [y])
      ih = rewrite sym $ reverseCons y zs in reverseReduced pTail
  in
  rewrite reverseCons x (y :: zs) in 
  rewrite reverseCons y zs in 
  snocReduced {ys = reverse zs} {last = y} {new = x} ih (notInvSwap notInv)

public export
invWordReduced : (x : FreeCarrier n) -> Reduced (invWord x.word)
invWordReduced x = reverseReduced $ mapInvReduced x

public export
inv : FreeCarrier n -> FreeCarrier n
inv u = MkFreeCarrier (invWord u.word) (invWordReduced u)

public export
unit : FreeCarrier n
unit = MkFreeCarrier [] RNil

public export
FreeSetoid : (n : Nat) -> Setoid
FreeSetoid n = MkSetoid
  { U = FreeCarrier n
  , equivalence = MkEquivalence
    { relation = \x, y        => (LetterSetoid n).ListEquality x.word y.word
    , reflexive = \x          => (LetterSetoid n).ListEqualityReflexive x.word
    , symmetric = \x, y, prf  => (LetterSetoid n).ListEqualitySymmetric _ _ prf
    , transitive = \x, y, z, prf1, prf2 =>
      (LetterSetoid n).ListEqualityTransitive _ _ _ prf1 prf2
    }
  }

public export
reduceFrontHomomorphism : (x, y : Letter n) ->
  (xs, ys : FreeCarrier n) ->
  (x_eq_y : x = y) ->
  (xs_eq_ys : (RawWordSetoid n).equivalence.relation xs.word ys.word) ->
  (FreeSetoid n).equivalence.relation (reduceFront x xs) (reduceFront y ys)
reduceFrontHomomorphism x y (MkFreeCarrier [] RNil) (MkFreeCarrier [] RNil) x_eq_y xs_eq_ys = [x_eq_y]
reduceFrontHomomorphism x y (MkFreeCarrier (z :: zs) r1) (MkFreeCarrier (w :: ws) r2) x_eq_y (z_eq_w :: zs_eq_ws)
  with (decEq z (invLetter x)) | (decEq w (invLetter y))
  _ | Yes _ | Yes _ = zs_eq_ws
  _ | No _ | No _ = x_eq_y :: z_eq_w :: zs_eq_ws
  _ | Yes prf | No nprf = absurd $ nprf $
    rewrite sym x_eq_y in 
    rewrite sym z_eq_w in 
    prf
  _ | No nprf | Yes prf  = absurd $ nprf $ 
    rewrite x_eq_y in 
    rewrite z_eq_w in 
    prf

public export
MulHomomorphism : {n : Nat} -> (x1, x2, y1, y2 : FreeCarrier n) ->
  (x1_eq_x2 : (FreeSetoid n).equivalence.relation x1 x2) ->
  (y1_eq_y2 : (FreeSetoid n).equivalence.relation y1 y2) ->
  (FreeSetoid n).equivalence.relation (mul x1 y1) (mul x2 y2)
MulHomomorphism (MkFreeCarrier [] r1) (MkFreeCarrier [] r2) y1 y2 x1_eq_x2 y1_eq_y2 = 
  rewrite reduceFreeWord y1 in 
  rewrite reduceFreeWord y2 in 
  y1_eq_y2
MulHomomorphism (MkFreeCarrier (x :: xs) r1) (MkFreeCarrier (y :: ys) r2) y1 y2 (x_eq_y :: xs_eq_ys) y1_eq_y2 =
  reduceFrontHomomorphism x y _ _ x_eq_y $
  MulHomomorphism (MkFreeCarrier xs $ tailReduced r1) (MkFreeCarrier ys $ tailReduced r2) y1 y2 xs_eq_ys y1_eq_y2

public export
reduceHomomorphism : {n : Nat} -> (x, y : RawWord n) ->
  (RawWordSetoid n).equivalence.relation x y ->
  (FreeSetoid n).equivalence.relation (reduce x) (reduce y)
reduceHomomorphism [] [] [] = []
reduceHomomorphism (x :: xs) (y :: ys) (x_eq_y :: xs_eq_ys) = 
  reduceFrontHomomorphism _ _ _ _ x_eq_y $ reduceHomomorphism xs ys xs_eq_ys

public export
InvHomomorphism : {n : Nat} -> (x, y : FreeCarrier n) ->
  (x_eq_y : (FreeSetoid n).equivalence.relation x y) ->
  (FreeSetoid n).equivalence.relation (inv x) (inv y)
InvHomomorphism x y x_eq_y = 
  reverseHomomorphic _ _ $ (ListMapHomomorphism invLetterHomomorphism).homomorphic _ _ x_eq_y
  
public export
FreeGroupStructureOver : (n : Nat) -> GroupStructure
FreeGroupStructureOver n = MkSetoidAlgebra
  { algebra = MkAlgebra (FreeCarrier n) $
      \case (Mono op) => case op of        -- NB: can't pattern match in one go otherwise the function is flagged as non-covering
              Neutral => unit
              Product => mul
            Inverse => inv
  , equivalence = (FreeSetoid n).equivalence
  , congruence = \case
    MkOp (Mono op) => case op of
      Neutral => \[], [], _ => Nil
      Product => \[x1, y1], [x2, y2], prf => MulHomomorphism x1 x2 y1 y2 (prf 0) (prf 1)
    MkOp Inverse => \[x], [y], prf => InvHomomorphism x y (prf 0)
  }

public export
mult : Nat -> FreeCarrier n -> FreeCarrier n
mult 0 _ = unit
mult (S k) x = mul x (mult k x)

public export
MonAction : {n : Nat} -> ActionData Nat (FreeCarrier n)
MonAction =
  [ mult
  , (FreeGroupStructureOver n).sem (Mono Neutral)
  , (FreeGroupStructureOver n).sem (Mono Product)]