module Frex.DistributiveCombination.Structure

import Frex.DistributiveCombination.Theory

import Frex.Signature
import Frex.Presentation
import Frex.Algebra
import Frex.Model
import Frex.Free

import Data.Setoid

import Data.Vect

%default total

parameters {A : Setoid} {pres : Presentation} {M : Model pres} {free_a : Free pres A}

  --------------------- EXTEND ----------------------

  public export
  extend : (A ~> cast M) -> (free_a .Data .Model ~> M)
  extend f = (free_a .UP .Exists $ MkModelOver M f) .H

  public export
  extend_preserves : (f : A ~> cast M) ->
    (A ~~> cast M) .equivalence .relation
          (((extend f) .H) . (free_a .Data .Env)) 
          f
  extend_preserves f = (free_a .UP .Exists $ MkModelOver M f) .preserves

  public export
  extend_cong : (f, g : A ~> cast M) ->
    (A ~~> cast M) .equivalence .relation f g -> 
    (free_a .Data .Model ~~> M) .equivalence .relation 
      (extend f)
      (extend g)
  extend_cong f g prf = 
    let Mg : pres `ModelOver` A
        Mg = MkModelOver M g
    in
    (free_a .UP .Unique Mg) 
    (MkHomomorphism (extend f) 
      ((A ~~> cast M).equivalence.transitive (((extend f) .H) . (free_a .Data .Env)) f g (extend_preserves f) prf))
    (free_a .UP .Exists Mg)

  --------------------- HELPERS FOR PSI ----------------------

  public export
  section : {k : Nat} -> {f : VectSetoid (S k) A ~> cast M} ->
  U A -> VectSetoid k A ~> cast M
  section x = MkSetoidHomomorphism
    (\xs => f.H $ x :: xs) $
    \y, z, prf => f.homomorphic (x :: y) (x :: z) $ 
    \case FZ => A .equivalence .reflexive _
          FS k => prf k

  public export
  step : {k : Nat} -> {f : VectSetoid (S k) A ~> cast M} ->
  Vect k (U (cast $ free_a .Data .Model)) -> A ~> cast M

  public export
  go : {k : Nat} -> {f : VectSetoid (S k) A ~> cast M} ->
        Vect (S k) (U (cast $ free_a .Data .Model)) -> U (cast M)

  --------------------- PSI and PSI_CONG ----------------------

  public export
  psi : {n : Nat} -> (f : VectSetoid n A ~> cast M) ->
    VectSetoid n (cast $ free_a .Data .Model) ~> cast M
  
  public export
  psi_cong : {n : Nat} -> (f, g : VectSetoid n A ~> cast M) ->
    (VectSetoid n A ~~> cast M).equivalence.relation f g ->
    (VectSetoid n (cast $ free_a .Data .Model) ~~> cast M).equivalence.relation
      (psi f)
      (psi g)

  --------------------- DEFINITIONS ----------------------

  step xs = MkSetoidHomomorphism
    (\x => (psi (section x)).H xs) $ 
    \x, y, prf => psi_cong (section x) (section y) 
    (\ys => f.homomorphic (x :: ys) (y :: ys) $
      \case FZ => prf
            FS k => A .equivalence .reflexive _) 
    xs

  go (x :: xs) = (extend (step xs)).H.H x

  psi {n = Z} f = 
    MkSetoidHomomorphism (\[] => f.H []) $
    \[],[],_ => M .equivalence .reflexive _
  psi {n = S k} f =
    MkSetoidHomomorphism (go {f}) $
    \(x :: xs), (y :: ys), prf => 
    CalcWith (cast M) $
    |~ (extend (step xs)).H.H x
    ~~ (extend (step ys)).H.H x 
        ... (extend_cong (step xs) (step ys)
            (\x => (psi (section {f} x)) .homomorphic xs ys (\i => prf (FS i))) $ x)
    ~~ (extend (step ys)).H.H y ... ((extend (step ys)) .H .homomorphic _ _ (prf 0))

  psi_cong {n = Z} f g f_eq_g [] = f_eq_g []
  psi_cong {n = S k} f g f_eq_g (x :: xs) = 
    extend_cong (step {f} xs) (step {f=g} xs) 
      (\x => psi_cong {n = k} (section {f} x) (section {f = g} x) (\xs => f_eq_g (x :: xs)) $ xs)
      $ x

  --------------------- LEMMAS ----------------------

  public export
  psi_extension : {n : Nat} -> (f : VectSetoid n A ~> cast M) ->
    (xs : Vect n (U A)) -> 
    (cast M) .equivalence .relation
      ((psi f) .H $ map (free_a .Data .Env .H) xs)
      (f .H $ xs)
  psi_extension {n = Z} f [] = (cast M) .equivalence .reflexive _
  psi_extension {n = S k} f (x :: xs) = 
    let eta : U A -> U $ cast $ free_a .Data .Model
        eta = free_a .Data .Env .H
    in
    CalcWith (cast M) $
    |~ (extend (step (map eta xs))).H.H (eta x)
    ~~ ((extend (step (map eta xs))) .H . (free_a .Data .Env)) .H x .=. (Refl)
    ~~ (step (map eta xs)).H x ... (extend_preserves (step (map eta xs)) x)
    ~~ (psi (section x)).H (map eta xs) .=. (Refl)
    ~~ (section x).H xs ... (psi_extension {n=k} (section x) xs)
    ~~ f.H (x :: xs) .=. (Refl)


-- parameters {presA : Presentation} {presM : Presentation} {X : Setoid} (free_A : (Y : Setoid) -> Free presA Y) (free_M : (Y : Setoid) -> Free presM Y)

--   A0 : presM `ModelOver` X
--   A0 = (free_M X).Data

--   A0carr : Setoid
--   A0carr = cast $ A0 .Model

--   -----------------------------------------------------------------

--   FA : Free presA A0carr
--   FA = free_A A0carr

--   FAcarr : Setoid
--   FAcarr = cast $ FA .Data .Model

--   M_algebra : SetoidAlgebra (presM .signature)
--   M_algebra = 
--         let psi_app : {n : Nat} -> (f : presM.signature.OpWithArity n) -> VectSetoid n (cast $ FA .Data .Model) ~> (cast $ FA .Data .Model)
--             psi_app f = psi ((FA .Data .Env) . (cast (MkOp f)))
--         in
--         MkSetoidAlgebra
--         { algebra     = MakeAlgebra (U FAcarr) $ \f => (psi_app f.snd) .H
--         , equivalence = FAcarr .equivalence
--         , congruence  = \f => (psi_app f.snd).homomorphic
--         }

--   lemma1 : {n : Nat} -> (t : Term (presM .signature) (Fin n)) -> 
--     (env : (Fin n) -> U A0carr) -> FAcarr .equivalence .relation
--       (M_algebra .Sem t ((FA .Data .Env .H) . env))
--       (FA .Data .Env .H $ (A0 .Sem) t env)
--   lemma1 (Done x) env = FAcarr .equivalence .reflexive _
--   lemma1 (Call f xs) env = ?def
--     -- CalcWith (cast M_algebra) $
--     -- |~ M_algebra .Sem (Call f xs) ((FA .Data .Env .H) . env)
--     -- ~~ M_algebra .Sem f (bindTerms {sig = presM .signature} {a = cast M_algebra} xs ((FA .Data .Env .H) . env)) .=. (Refl)
--     -- ~~ M_algebra .Sem f (map (flip M_algebra .Sem ((FA .Data .Env .H) . env)) xs) ... (?prf1)
--     -- ~~ ?eq1 ... (?prf2)
--     -- psi_extension ((FA .Data .Env) . (cast $ MkOp (f .snd))) ?xs

--   A2 : presM `ModelOver` A0carr
--   A2 =        
--     MkModelOver
--     { Model = MkModel
--       { Algebra  = M_algebra
--       , Validate = \ax, env => ?validates
--       }
--     , Env   = FA .Data .Env
--     }

public export
DistributiveCombinationStructure' : {additive : Presentation} -> {multiplicative : Presentation} ->
  (X : Setoid) -> (freeM : Free multiplicative X) -> (freeA : Free additive (cast freeM.Data.Model)) ->
  SetoidAlgebra (CoproductSignature additive.signature multiplicative.signature)
DistributiveCombinationStructure' x freeM freeA =
  let psi_app : {n : Nat} -> (f : multiplicative.signature.OpWithArity n) -> VectSetoid n (cast $ freeA.Data.Model) ~> (cast $ freeA.Data.Model)
      psi_app f = psi ((freeA.Data.Env) . (cast (MkOp f)))
  in
  MkSetoidAlgebra
  { algebra = MakeAlgebra (U $ cast freeA.Data.Model) $
    \case (MkOp (Left f)) => freeA.Data.Model.Sem (MkOp f)
          (MkOp (Right f)) => (psi_app f).H
  , equivalence = (cast freeA.Data.Model).equivalence
  , congruence = \case (MkOp (Left f)) => freeA.Data.Model.Algebra.congruence (MkOp f)
                       (MkOp (Right f)) => (psi_app f).homomorphic
  }

public export
DistributiveCombinationStructure : {additive : Presentation} -> {multiplicative : Presentation} ->
  (X : Setoid) -> (free_A : (Y : Setoid) -> Free additive Y) -> (free_M : (Y : Setoid) -> Free multiplicative Y) ->
  SetoidAlgebra (CoproductSignature additive.signature multiplicative.signature)
DistributiveCombinationStructure x free_A free_M =
  let freeM : Free multiplicative x
      freeM = free_M x
      freeA : Free additive (cast freeM.Data.Model)
      freeA = free_A $ cast freeM.Data.Model
  in DistributiveCombinationStructure' x freeM freeA