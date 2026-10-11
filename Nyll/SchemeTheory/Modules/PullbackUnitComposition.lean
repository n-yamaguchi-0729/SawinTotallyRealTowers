/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Units and composition of pullback functors

The unit for a composite scheme morphism agrees with the successive units
after the canonical pullback composition comparison.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_unit_app_comp_pullbackComp_inv

universe u

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.unit_app_comp_pullbackComp_inv
    {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ f)).unit.app M).app U ≫
        ((Scheme.Modules.pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp
      (pullbackPushforwardAdjunction g))
    (pullbackPushforwardAdjunction (g ≫ f)) (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv] at h
  have h' := congrArg (fun t => Hom.app t U) h
  simp only [Hom.comp_app, Adjunction.comp_unit_app, pushforward_map_app,
      pushforwardComp_hom_app_app,
    Functor.comp_obj] at h'
  erw [Category.comp_id] at h'
  exact h'.symm
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_unit_app_comp_pullbackComp_inv
end ProofImplementation
