/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.Invertible
import Nyll.SchemeTheory.Modules.AffineSectionsBaseChange
import Nyll.SchemeTheory.Affine.PullbackSectionsPushout
import Mathlib.RingTheory.IsTensorProduct

/-! Tensor base change for sections over affine opens. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- Flat-base section comparison over an affine open in a pullback square. -/
theorem exists_tensorProduct_linearEquiv_sections_pullback_preimage_of_isAffineOpen
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S))
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (U : X.Opens) (hU : IsAffineOpen U) :
    let : Algebra S Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U
      le_top).hom.toAlgebra
    let : Module S Γ(M, U) := Module.compHom _ (algebraMap S Γ(X, U))
    let : Algebra S' Γ(X', c ⁻¹ᵁ U) :=
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top).hom.toAlgebra
    let : Module S' Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U) :=
      Module.compHom _ (algebraMap S' Γ(X', c ⁻¹ᵁ U))
    ∃ β : S' ⊗[S] Γ(M, U) ≃ₗ[S'] Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U),
      ∀ s : Γ(M, U), β (1 ⊗ₜ s) = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        M).app U) s := by
  intro iA iSM iB iS'M
  obtain ⟨hcU, hpush⟩ :=
    AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback f f' c hc U hU
  obtain ⟨β₀, hβ₀⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_baseChange_sections_linearEquiv_pullback
      c hM U hU hcU
  let iAB : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.app U).hom.toAlgebra
  let iSB : Algebra S Γ(X', c ⁻¹ᵁ U) :=
    ((algebraMap Γ(X, U) Γ(X', c ⁻¹ᵁ U)).comp (algebraMap S Γ(X, U))).toAlgebra
  have tSAB : IsScalarTower S Γ(X, U) Γ(X', c ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq' rfl
  have hw : f' ≫ Spec.map (CommRingCat.ofHom (algebraMap S S')) = c ≫ f := hc.w.symm
  have h1 : (Spec.map (CommRingCat.ofHom (algebraMap S S'))).appTop ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top =
      (c ≫ f).appLE ⊤ (c ⁻¹ᵁ U) le_top := by
    change (Spec.map (CommRingCat.ofHom (algebraMap S S'))).appTop ≫
        (f'.appTop ≫ X'.presheaf.map (homOfLE le_top).op) =
      (c ≫ f).appTop ≫ X'.presheaf.map (homOfLE le_top).op
    rw [← Category.assoc, ← Scheme.Hom.comp_appTop, hw]
  have h3 : f.appLE ⊤ U le_top ≫ c.app U = (c ≫ f).appLE ⊤ (c ⁻¹ᵁ U) le_top := by
    exact (congrArg (fun k => f.appLE ⊤ U le_top ≫ k)
      (Scheme.Hom.appLE_eq_app c).symm).trans
        (Scheme.Hom.appLE_comp_appLE c f ⊤ U (c ⁻¹ᵁ U) le_top le_rfl)
  have E : CommRingCat.ofHom (algebraMap S S') ≫
      ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appLE ⊤ (c ⁻¹ᵁ U) le_top) =
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appLE ⊤ U le_top) ≫ c.app U := by
    rw [Scheme.ΓSpecIso_inv_naturality_assoc, Category.assoc, h1, h3]
  have tSS'B : IsScalarTower S S' Γ(X', c ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun s => (congrArg (fun k => k.hom s) E).symm
  have : IsScalarTower S Γ(X, U) Γ(M, U) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower S' Γ(X', c ⁻¹ᵁ U) Γ((Scheme.Modules.pullback c).obj M, c ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have key : c.appLE U (c ⁻¹ᵁ U) le_rfl = c.app U := Scheme.Hom.appLE_eq_app c
  have tSAB' : (let : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      IsScalarTower S Γ(X, U) Γ(X', c ⁻¹ᵁ U)) := by
    let : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) := (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    exact IsScalarTower.of_algebraMap_eq fun s => by
      change _ = (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom (algebraMap S Γ(X, U) s)
      rw [key]; rfl
  have : Algebra.IsPushout S S' Γ(X, U) Γ(X', c ⁻¹ᵁ U) := by
    change ∀ [algSB : Algebra S Γ(X', c ⁻¹ᵁ U)]
        [towerSS : IsScalarTower S S' Γ(X', c ⁻¹ᵁ U)]
        [towerSA : (let : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) :=
          (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra;
          IsScalarTower S Γ(X, U) Γ(X', c ⁻¹ᵁ U))],
        (let : Algebra Γ(X, U) Γ(X', c ⁻¹ᵁ U) :=
          (c.appLE U (c ⁻¹ᵁ U) le_rfl).hom.toAlgebra;
          Algebra.IsPushout S S' Γ(X, U) Γ(X', c ⁻¹ᵁ U)) at hpush
    have hP := hpush (algSB := iSB) (towerSS := tSS'B) (towerSA := tSAB')
    convert hP using 2
    rw [key]
  refine ⟨(Algebra.IsPushout.cancelBaseChange S S' Γ(X, U) Γ(X', c ⁻¹ᵁ U) Γ(M, U)).symm ≪≫ₗ
    β₀.restrictScalars S', fun s => ?_⟩
  rw [LinearEquiv.trans_apply, Algebra.IsPushout.cancelBaseChange_symm_tmul, map_one,
    LinearEquiv.restrictScalars_apply, hβ₀]

end AlgebraicGeometry.Scheme.Modules.IsInvertible
