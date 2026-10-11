/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted proof at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_tensorPowAdd_hom_app_tensorSections_tensorPowSection.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorPowerComparison
import Nyll.SchemeTheory.Modules.TensorSectionRightUnitor
import Nyll.SchemeTheory.Modules.TensorSectionAssociator
import Nyll.SchemeTheory.Modules.TensorSectionMaps
import Nyll.SchemeTheory.Modules.TensorSections

/-!
# Multiplication of tensor powers of a local section
-/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The addition comparison multiplies powers of the same local section. -/
theorem tensorPowAdd_hom_app_tensorSections_tensorPowSection
    {X : Scheme.{u}} {L : X.Modules} {U : X.Opens} (g : Γ(L, U)) (m n : ℕ) :
    (Scheme.Modules.tensorPowAdd L m n).hom.app U
        (Scheme.Modules.tensorSections (L := L.tensorPow m) (M := L.tensorPow n)
          (Scheme.Modules.tensorPowSection g m) (Scheme.Modules.tensorPowSection g n)) =
      Scheme.Modules.tensorPowSection g (m + n) := by
  induction n with
  | zero =>
    have h := rightUnitor_hom_app_tensorSections (N := L.tensorPow m) (U := U)
      (tensorPowSection g m) (1 : Γ(X, U))
    rw [one_smul] at h
    exact h
  | succ n ih =>
    change ((α_ (L.tensorPow m) (L.tensorPow n) L).symm ≪≫
        whiskerRightIso (tensorPowAdd L m n) L).hom.app U
        (tensorSections (L := L.tensorPow m) (M := L.tensorPow n ⊗ L) (tensorPowSection g m)
          (tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection g n) g)) =
      tensorSections (L := L.tensorPow (m + n)) (M := L) (tensorPowSection g (m + n)) g
    have hα : (α_ (L.tensorPow m) (L.tensorPow n) L).inv.app U
        (tensorSections (L := L.tensorPow m) (M := L.tensorPow n ⊗ L) (tensorPowSection g m)
          (tensorSections (L := L.tensorPow n) (M := L) (tensorPowSection g n) g)) =
        tensorSections (L := L.tensorPow m ⊗ L.tensorPow n) (M := L)
          (tensorSections (L := L.tensorPow m) (M := L.tensorPow n)
            (tensorPowSection g m) (tensorPowSection g n)) g := by
      rw [← associator_hom_app_tensorSections, ← CategoryTheory.comp_apply,
        ← Scheme.Modules.Hom.comp_app,
        Iso.hom_inv_id, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]
    rw [Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Scheme.Modules.Hom.comp_app,
      CategoryTheory.comp_apply, hα, ← tensorHom_id, tensorHom_app_tensorSections,
      ih, Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

end AlgebraicGeometry.Scheme.Modules
