module Frexlet.Monoid.Involutive.Free

import Frex
import Frexlet.Monoid.Involutive.Theory
import Frexlet.Monoid.Involutive.Properties
import Frexlet.Monoid.Involutive.Notation
import Frexlet.Monoid.Involutive.Frex
import Frexlet.Monoid.Notation
import Notation.Multiplicative
import Frexlet.Monoid.Free

public export
Initial : Free InvolutiveMonoidTheory (cast Void)
Initial =
  let trivial : Free MonoidTheory (cast Void)
      trivial = FreeMonoidVoid
      model : InvolutiveMonoidTheory `ModelOver` (cast Void)
      model = MkModelOver
        { Model = MkInvolutiveMonoid
          { monoid = trivial.Data.Model
          , involution = mate $ \x => x
          , involutivity = \env => Refl
          , antidistributivity = \env => Refl
          }
        , Env = mate $ \case _ impossible
        }
      castOther : (InvolutiveMonoidTheory `ModelOver` (cast Void)) ->
                            (MonoidTheory `ModelOver` (cast Void))
      castOther other = MkModelOver (cast other.Model) other.Env
  in MkFree
  { Data = model
  , UP = IsFree
    { Exists = \other =>
        let h : trivial.Data ~> (castOther other)
            h = trivial.UP.Exists (castOther other)
        in MkHomomorphism
          { H = MkSetoidHomomorphism
                { H = h.H.H
                , preserves = \case
                    MkOp (Mono op)  => h.H.preserves (MkOp op)
                    MkOp Involution => \[x] =>
                      let %hint notation : InvMult1 (U other.Model)
                          notation = other.Model.Notation1
                      in CalcWith (cast other.Model) $
                      |~ h.H.H.H x
                      ~~ I1      .=.(Refl)
                      ~~ I1 .inv ..<(invNeutral other.Model)
                }
          , preserves = h.preserves
          }
    , Unique = \other, h1, h2 =>
      let monoid : MonoidTheory `ModelOver` (cast Void)
          monoid = MkModelOver (cast {to = Monoid} other.Model) other.Env
          prime : (model ~> other) -> trivial.Data ~> monoid
          prime h = MkHomomorphism
            { H = MkSetoidHomomorphism
                { H = h.H.H
                , preserves = \case
                    (MkOp Neutral) => h.H.preserves (MkOp (Mono Neutral))
                    (MkOp Product) => h.H.preserves (MkOp (Mono Product))
                }
            , preserves = \case _ impossible
            }
      in trivial.UP.Unique (castOther other) (prime h1) (prime h2)
    }
  }

public export
FreeInvolutiveMonoidOver : (n : Nat) -> Free InvolutiveMonoidTheory (cast $ Fin n)
FreeInvolutiveMonoidOver n = ByFrex Initial (Involutive.Frex.Frex _)

public export
FreeInvolutiveMonoid : (s : Setoid) -> Free InvolutiveMonoidTheory s
FreeInvolutiveMonoid s = ByFrex Initial (Involutive.Frex.Frex _)