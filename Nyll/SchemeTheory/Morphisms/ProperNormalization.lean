/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper relative normalization

The canonical relative normalization of a universally closed qcqs morphism
has the same sections as the source above every affine open of the base.
Over an affine base this identifies the actual normalization with the
spectrum of global sections. In particular, the first morphism of a proper
relative normalization is proper and surjective.

These are the geometric and section-theoretic parts of Stacks 03GY and 03H2.
Geometric connectedness of the first morphism is not asserted here.

References:
* https://stacks.math.columbia.edu/tag/03GY
* https://stacks.math.columbia.edu/tag/03H2
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Universal closedness makes sections integral above every affine base open. -/
lemma isIntegral_app_of_universallyClosed [UniversallyClosed f]
    {U : S.Opens} (hU : IsAffineOpen U) :
    (f.app U).hom.IsIntegral := by
  have : IsAffine U := hU
  have h := isIntegral_appTop_of_universallyClosed (f ∣_ U)
  have : (RingHom.toMorphismProperty RingHom.IsIntegral).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  have hComparison := MorphismProperty.arrow_mk_iso_iff
    (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl)
  change ((f.resLE U (f ⁻¹ᵁ U) le_rfl).appTop).hom.IsIntegral ↔
    (f.appLE U (f ⁻¹ᵁ U) le_rfl).hom.IsIntegral at hComparison
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at hComparison
  exact hComparison.mp h

namespace Scheme.Hom

/-- The integral closure used to build the normalization is the full section ring
for a universally closed morphism. -/
lemma integralClosure_eq_top_of_universallyClosed [UniversallyClosed f]
    {U : S.Opens} (hU : IsAffineOpen U) :
    let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) = ⊤ := by
  let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  rw [integralClosure_eq_top_iff, ← algebraMap_isIntegral_iff,
    RingHom.algebraMap_toAlgebra]
  exact isIntegral_app_of_universallyClosed f hU

variable [QuasiCompact f] [QuasiSeparated f]

instance isAffine_normalization [IsAffine S] : IsAffine f.normalization :=
  isAffine_of_isAffineHom f.fromNormalization

/-- Above an affine base open, the canonical map to the relative normalization
induces an isomorphism on sections. -/
lemma isIso_toNormalization_app_of_universallyClosed [UniversallyClosed f]
    {U : S.Opens} (hU : IsAffineOpen U) :
    IsIso (f.toNormalization.app (f.fromNormalization ⁻¹ᵁ U)) := by
  let : Algebra Γ(S, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have hval : IsIso (CommRingCat.ofHom
      (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom) := by
    rw [f.integralClosure_eq_top_of_universallyClosed hU]
    exact inferInstanceAs (IsIso
      (Subalgebra.topEquiv (R := Γ(S, U))
        (A := Γ(X, f ⁻¹ᵁ U))).toCommRingCatIso.hom)
  rw [f.toNormalization_app_preimage ⟨U, hU⟩]
  apply IsIso.comp_isIso' (inferInstanceAs (IsIso (f.normalizationObjIso hU).hom))
  apply IsIso.comp_isIso' hval
  infer_instance

instance isIso_toNormalization_appTop_of_universallyClosed
    [UniversallyClosed f] [IsAffine S] : IsIso f.toNormalization.appTop := by
  exact f.isIso_toNormalization_app_of_universallyClosed (isAffineOpen_top S)

/-- Over an affine base, the native relative normalization of a universally
closed qcqs morphism is the spectrum of the source's global sections. -/
def normalizationIsoSpec [UniversallyClosed f] [IsAffine S] :
    f.normalization ≅ Spec Γ(X, ⊤) :=
  f.normalization.isoSpec ≪≫
    (asIso (Spec.map f.toNormalization.appTop)).symm

/-- The identification with the spectrum of global sections carries the native
normalization map to the canonical affinization map. -/
@[reassoc]
lemma toNormalization_normalizationIsoSpec_hom
    [UniversallyClosed f] [IsAffine S] :
    f.toNormalization ≫ f.normalizationIsoSpec.hom = X.toSpecΓ := by
  change f.toNormalization ≫ f.normalization.toSpecΓ ≫
      inv (Spec.map f.toNormalization.appTop) = X.toSpecΓ
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc,
    IsIso.hom_inv_id, Category.comp_id]

instance isProper_toNormalization [IsProper f] : IsProper f.toNormalization := by
  have : IsProper (f.toNormalization ≫ f.fromNormalization) := by
    rw [f.toNormalization_fromNormalization]
    infer_instance
  exact IsProper.of_comp f.toNormalization f.fromNormalization

end Scheme.Hom

end AlgebraicGeometry
