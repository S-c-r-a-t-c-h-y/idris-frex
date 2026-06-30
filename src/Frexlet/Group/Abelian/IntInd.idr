module Frexlet.Group.Abelian.IntInd

public export
data IntInd : Type where
  Pos : Nat -> IntInd
  Neg : Nat -> IntInd  -- Neg k means -(S k)

public export
plus : IntInd -> IntInd -> IntInd

public export
times : IntInd -> IntInd -> IntInd

public export
minus : IntInd -> IntInd -> IntInd

public export
neg : IntInd -> IntInd

public export
fromInteger : Integer -> IntInd
fromInteger i = 
  if i < 0 then Neg (fromInteger (i + 1))
           else Pos (fromInteger i)

public export
Num IntInd where
  (+) = plus
  (*) = times
  fromInteger = IntInd.fromInteger

public export
Neg IntInd where
  negate = neg
  (-) = minus