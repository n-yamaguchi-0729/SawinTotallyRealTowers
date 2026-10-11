/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.Ring.Constructions
import Nyll.SchemeTheory.Modules.SectionsAlgebra

/-!
# Scheme Hom is Affine Open preimage and is Pushout of is Pullback
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry


universe u v

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (isPushout_appTop_of_isPullback Scheme.Hom IsAffine
  isPullback_morphismRestrict Spec Spec.map Scheme Scheme.Hom.appTop Scheme.Opens.topIso_hom
  Scheme.Hom.comp_appTop IsAffineOpen Scheme.Opens Scheme.Hom.appLE_map Scheme.Hom.app_eq_appLE
  Scheme.Hom.resLE_eq_morphismRestrict Scheme.Hom.resLE_app_top Scheme.ΓSpecIso_naturality
  IsAffineHom Scheme.Opens.ι_appTop Scheme.ΓSpecIso)


open _root_.AlgebraicGeometry


namespace Scheme
export _root_.AlgebraicGeometry.Scheme (Hom Γ topIso_hom topIso Hom.appTop Opens.topIso_hom
  Hom.comp_appTop Opens Hom.appLE_map Hom.app_eq_appLE Hom.resLE_eq_morphismRestrict
  Hom.resLE_app_top ΓSpecIso_naturality Opens.ι_appTop ΓSpecIso)
namespace Hom
export _root_.AlgebraicGeometry.Scheme.Hom (appTop comp_appTop appLE_map app_eq_appLE
  resLE_eq_morphismRestrict resLE_app_top appLE sectionsAlgebra)
end Scheme.Hom

open scoped _root_.AlgebraicGeometry.Scheme in
open scoped _root_.AlgebraicGeometry.Scheme.Hom in
theorem Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback_aux
    {A : Type u} [CommRing A] {Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (U : Y.Opens) :
    (U.ι ≫ gY).appTop ≫ U.topIso.hom = gY.appLE ⊤ U le_top := by
  have hmap : U.ι.appTop ≫ U.topIso.hom =
      Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op := by
    change Y.presheaf.map (homOfLE (le_top : U.ι ''ᵁ ⊤ ≤ ⊤)).op ≫
      Y.presheaf.map (eqToHom U.ι_image_top.symm).op =
        Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    rw [← Functor.map_comp]
    congr 1
  exact (congrArg
    (fun m : Γ(Spec (CommRingCat.of A), ⊤) ⟶ Γ(↑U, ⊤) => m ≫ U.topIso.hom)
    (Scheme.Hom.comp_appTop U.ι gY)).trans
      ((Category.assoc gY.appTop U.ι.appTop U.topIso.hom).trans
        (congrArg (fun m : Γ(Y, ⊤) ⟶ Γ(Y, U) => gY.appTop ≫ m) hmap))

end AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (U : Y.Opens) (hU : IsAffineOpen U) :
    IsAffineOpen (φ ⁻¹ᵁ U) ∧
      letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
      letI : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
      ∀ [Algebra A Γ(X, φ ⁻¹ᵁ U)] [IsScalarTower A B Γ(X, φ ⁻¹ᵁ U)]
        [IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)],
        Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => IsAffineHom h) :=
    isAffineHom_isStableUnderBaseChange
  have : IsAffineHom φ := hbc.of_isPullback hφ.flip inferInstance
  have hV : IsAffineOpen (φ ⁻¹ᵁ U) := hU.preimage φ
  refine ⟨hV, ?_⟩
  intro algA ist₁ ist₂
  have sq : IsPullback (φ ∣_ U) ((φ ⁻¹ᵁ U).ι ≫ gX) (U.ι ≫ gY)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) :=
    (isPullback_morphismRestrict φ U).paste_vert hφ
  let _ : IsAffine U := hU
  let _ : IsAffine (φ ⁻¹ᵁ U) := hV
  have H := isPushout_appTop_of_isPullback sq.flip
  let _ := gY.sectionsAlgebra U
  let _ := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
  let _ : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  refine (CommRingCat.isPushout_iff_isPushout (R := A) (R' := B) (S := Γ(Y, U))
    (S' := Γ(X, φ ⁻¹ᵁ U))).mp ?_
  have e₁ : CommRingCat.ofHom (algebraMap A Γ(Y, U)) =
      (Scheme.ΓSpecIso (.of A)).inv ≫ gY.appLE ⊤ U le_top := rfl
  have e₂ : CommRingCat.ofHom (algebraMap B Γ(X, φ ⁻¹ᵁ U)) =
      (Scheme.ΓSpecIso (.of B)).inv ≫ gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top := rfl
  have e₃ : CommRingCat.ofHom (algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U)) =
      φ.appLE U (φ ⁻¹ᵁ U) le_rfl := rfl
  refine H.of_iso (Scheme.ΓSpecIso (.of A)) (Scheme.ΓSpecIso (.of B)) U.topIso (φ ⁻¹ᵁ U).topIso
    ?_ ?_ ?_ ?_
  · exact Scheme.ΓSpecIso_naturality _
  · rw [e₁, Iso.hom_inv_id_assoc]
    exact AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback_aux gY U
  · rw [e₂, Iso.hom_inv_id_assoc]
    exact AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback_aux gX (φ
      ⁻¹ᵁ U)
  · rw [e₃, ← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top,
      Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
end Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
