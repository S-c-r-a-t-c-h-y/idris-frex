module Data.Relation

%default total

public export
0 Rel : Type -> Type
Rel a = a -> a -> Type

public export
interface DecRel (rel : Relation.Rel t) where
  decOrd : (x1 : t) -> (x2 : t) -> Dec (rel x1 x2)

export infix 5 ~>
public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y
