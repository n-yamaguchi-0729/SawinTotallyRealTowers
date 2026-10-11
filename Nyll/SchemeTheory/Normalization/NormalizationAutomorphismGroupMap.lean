/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.Normalization.IntegralClosureAutomorphismRestriction
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Normalization on automorphism group objects

Defines the coefficient automorphism group as a group object and the induced group morphism
obtained by restriction to the normalization.
-/

noncomputable section

namespace SchemeTheory

universe u v

/-- The native group of the original coefficient automorphisms. -/
def commAlgAutomorphismGroup (A : Type u) [CommRing A] (C : CommAlgCat.{v} A) : GrpCat.{v} :=
  GrpCat.of (C ≃ₐ[A] C)

/-- Actual normalization functoriality on coefficient automorphism groups. -/
def normalizationAutomorphismGroupMap (A : Type u) [CommRing A] (C : CommAlgCat.{v} A) :
    GrpCat.Hom (commAlgAutomorphismGroup A C)
      (commAlgAutomorphismGroup A (normalizationCommAlgCat A C)) where
  hom' := integralClosureAutHom A C

end SchemeTheory

end
