/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.Algebra.Ring.Idempotent

/-!
# Descending idempotent sections through affine-transition limits

A global section descends to a stage, and its idempotency equation holds at
a further stage. Both the section and the equation are actually constructed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- Every idempotent global section on an affine-transition limit is the
pullback of an actual idempotent at a stage. -/
theorem exists_idempotent_appTop_eq_of_isLimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i k} (f : i ⟶ k), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    (e : Γ(c.pt, ⊤)) (he : IsIdempotentElem e) :
    ∃ (i : I) (t : Γ(D.obj i, ⊤)), IsIdempotentElem t ∧ (c.π.app i).appTop t = e := by
  obtain ⟨i, t, ht⟩ := exists_appTop_π_eq_of_isLimit D c hc e
  have hzero : (c.π.app i).appTop (t * t - t) = 0 := by
    rw [map_sub, map_mul, ← ht, he, sub_self]
  obtain ⟨k, f, hf⟩ := exists_appTop_map_eq_zero_of_isLimit D c hc (t * t - t) hzero
  refine ⟨k, (D.map f).appTop t, ?_, ?_⟩
  · change (D.map f).appTop t * (D.map f).appTop t = (D.map f).appTop t
    rw [map_sub, map_mul, sub_eq_zero] at hf
    exact hf
  · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, c.w f]
    exact ht.symm

end AlgebraicGeometry
