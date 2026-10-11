/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.Descent.LocalStageResidueComparison
import Nyll.SchemeTheory.Descent.NoetherianImageResidueLimit
import Nyll.SchemeTheory.Descent.AffineTransitionIdempotents
import Nyll.SchemeTheory.Morphisms.NoetherianProperFiberSections
import Mathlib.RingTheory.Localization.Submodule

/-!
# Lifting closed-fiber idempotents from actual Noetherian image stages

An idempotent on the original fiber descends to an actual Noetherian image
stage. Localizing that stage at the contracted closed point permits the
Noetherian proper-section theorem to lift it. Pullback of that section gives
an actual global section on the original closed subscheme.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.LocalStageResidue

universe u

variable {B A : Type u} [CommRing B] [CommRing A] [IsLocalRing A]
variable (φ : B →+* A) {P X : Scheme.{u}}
variable (q : P ⟶ Spec (CommRingCat.of B))
variable (f : X ⟶ Spec (CommRingCat.of A)) (t : X ⟶ P)
variable (w : t ≫ q = f ≫ Spec.map (CommRingCat.ofHom φ))

/-- A stage-fiber idempotent lifts to a section on the original scheme by
localizing the actual Noetherian stage at the contracted closed point. -/
theorem exists_appTop_eq_of_isIdempotentElem [IsNoetherianRing B] [IsProper q]
    (e : Γ(pullback q (stageResidueSpec φ), ⊤)) (he : IsIdempotentElem e) :
    ∃ a : Γ(X, ⊤),
      (pullback.fst f (topResidueSpec (A := A))).appTop a =
        (topFiberMap φ q f t w).appTop e := by
  let E := (fiber_isPullback φ q).isoPullback
  obtain ⟨a, ha⟩ := exists_appTop_eq_of_isProper_of_surjective_of_isIdempotentElem
    (localizedBaseMap φ q) (IsLocalRing.residue (Localization.AtPrime (prime φ)))
    IsLocalRing.residue_surjective (E.inv.appTop e) (he.map E.inv.appTop.hom)
  have heq : (fiberToLocalized φ q).appTop a = e := by
    calc
      (fiberToLocalized φ q).appTop a =
          E.hom.appTop ((pullback.fst (localizedBaseMap φ q) (residueSpec φ)).appTop a) := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          IsPullback.isoPullback_hom_fst]
      _ = E.hom.appTop (E.inv.appTop e) := congrArg E.hom.appTop ha
      _ = e := by
        rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
          E.hom_inv_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]
  refine ⟨(lift φ q f t w).appTop a, ?_⟩
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← topFiberMap_toLocalized, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, heq]

end AlgebraicGeometry.LocalStageResidue

namespace AlgebraicGeometry.NoetherianImageApproximation

universe u

variable (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable [IsNoetherianRing A₀] [IsLocalRing A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsProper f₀]
variable {Z : Scheme.{u}} (j : Z ⟶ (ambientCone A₀ A f₀).pt) [IsClosedImmersion j]

/-- A closed-fiber idempotent of the original closed subscheme is the
restriction of an actual global section, with no Noetherian assumption on
the original local base or finite-presentation assumption on the subscheme. -/
theorem exists_appTop_eq_of_closedFiber_isIdempotentElem
    (e : Γ(originalResidueFiber A₀ A f₀ j (IsLocalRing.maximalIdeal A), ⊤))
    (he : IsIdempotentElem e) :
    ∃ a : Γ(Z, ⊤),
      (pullback.fst (originalBaseMap A₀ A f₀ j)
        (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A))).appTop a = e := by
  obtain ⟨i, ei, hi, hei⟩ := exists_idempotent_appTop_eq_of_isLimit
    (residueFiberDiagram A₀ A f₀ j (IsLocalRing.maximalIdeal A))
    (residueFiberCone A₀ A f₀ j (IsLocalRing.maximalIdeal A))
    (residueFiberConeIsLimit A₀ A f₀ j (IsLocalRing.maximalIdeal A)) e he
  have : IsNoetherianRing i.unop.1 := stageRing_isNoetherian A₀ A i
  have w : (cone A₀ A f₀ j).π.app i ≫ baseMap A₀ A f₀ j i =
      originalBaseMap A₀ A f₀ j ≫ Spec.map (CommRingCat.ofHom i.unop.1.val.toRingHom) := by
    exact cone_projection_baseMap A₀ A f₀ j i
  obtain ⟨a, ha⟩ := LocalStageResidue.exists_appTop_eq_of_isIdempotentElem
    i.unop.1.val.toRingHom (baseMap A₀ A f₀ j i) (originalBaseMap A₀ A f₀ j)
    ((cone A₀ A f₀ j).π.app i) w ei hi
  exact ⟨a, ha.trans hei⟩

end AlgebraicGeometry.NoetherianImageApproximation
