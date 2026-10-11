/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Restriction of scalars on automorphism groups

Bundles algebra automorphisms as group objects and constructs the group morphism that restricts
their scalars along an algebra tower.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- The actual Galois automorphism group, retained as its native group object. -/
def galoisGroupObject (K : Type u) (L : Type v)
    [CommRing K] [CommRing L] [Algebra K L] : GrpCat.{v} :=
  GrpCat.of (L ≃ₐ[K] L)

/-- Restricting the original K-linear action to its original A-coefficients. -/
def scalarRestrictionGroupMap
    (A : Type u) (K : Type v) [CommRing A] [Field K] [Algebra A K]
    (C : CommAlgCat.{w} A) [Algebra K C] [IsScalarTower A K C] :
    GrpCat.Hom (galoisGroupObject K C) (commAlgAutomorphismGroup A C) where
  hom' := AlgEquiv.restrictScalarsHom A

end SchemeTheory

end
