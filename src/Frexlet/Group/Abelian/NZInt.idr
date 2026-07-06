module Frexlet.Group.Abelian.NZInt

public export
data NZInt = Pos Nat -- S n
           | Neg Nat -- - (S n)

public export
Cast NZInt Integer where
  cast (Pos k) = cast (S k)
  cast (Neg k) = - cast (S k)

public export
plus : NZInt -> NZInt -> Maybe NZInt
plus (Pos k) (Pos j) = Just $ Pos (k + j)
plus (Pos 0) (Neg 0) = Nothing
plus (Pos 0) (Neg (S k)) = Just $ Neg k
plus (Pos (S k)) (Neg 0) = Just $ Pos k
plus (Pos (S k)) (Neg (S j)) = plus (Pos k) (Neg j)
plus (Neg 0) (Pos 0) = Nothing
plus (Neg 0) (Pos (S k)) = Just $ Pos k
plus (Neg (S k)) (Pos 0) = Just $ Neg k
plus (Neg (S k)) (Pos (S j)) = plus (Neg k) (Pos j)
plus (Neg k) (Neg j) = Just $ Neg (k + j)

public export
neg : NZInt -> NZInt
neg (Pos k) = Neg k
neg (Neg k) = Pos k
