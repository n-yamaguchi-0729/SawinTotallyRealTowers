/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ProperNormalization
import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Topology.Sheaves.Functors

/-!
# Structure-sheaf pushforward for affine relative normalization

For a qcqs morphism to an affine scheme, an isomorphism on global sections
extends to an isomorphism of the structure sheaf with its pushforward.
Flat base change supplies the assertion on affine opens, and the sheaf
basis criterion supplies it on all opens. Applied to the section isomorphism
of a universally closed normalization, this proves the pushforward assertion
for the actual normalization map over an affine base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- For a qcqs morphism to an affine scheme, a global-sections isomorphism
remains an isomorphism on every affine target open. -/
lemma isIso_app_of_isIso_appTop [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] [IsIso f.appTop] {U : S.Opens} (hU : IsAffineOpen U) :
    IsIso (f.app U) := by
  have : IsAffine U := hU
  have hSections := isPushout_appTop_of_flat f U.ι
  let e : (f ⁻¹ᵁ U).toScheme ≅ pullback f U.ι :=
    (isPullback_morphismRestrict f U).flip.isoPullback
  have he : IsIso e.hom.appTop := (Scheme.Γ.mapIso e.op).isIso_hom
  have hRestrict : IsIso (f ∣_ U).appTop := by
    rw [← (isPullback_morphismRestrict f U).flip.isoPullback_hom_snd,
      Scheme.Hom.comp_appTop]
    exact IsIso.comp_isIso' hSections.isIso_inr_of_isIso he
  have hComparison := MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.isomorphisms CommRingCat)
    (arrowResLEAppIso f U (f ⁻¹ᵁ U) le_rfl)
  change IsIso (f.resLE U (f ⁻¹ᵁ U) le_rfl).appTop ↔
    IsIso (f.appLE U (f ⁻¹ᵁ U) le_rfl) at hComparison
  rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at hComparison
  exact hComparison.mp hRestrict

/-- Affine-local flat base change and the sheaf basis criterion extend the
global-sections isomorphism of a qcqs morphism to its full sheaf map. -/
lemma isIso_c_of_isIso_appTop [QuasiCompact f] [QuasiSeparated f]
    [IsAffine S] [IsIso f.appTop] : IsIso f.c := by
  let φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf :=
    ⟨f.c⟩
  have hBasis : Opens.IsBasis
      (Set.range (fun U : S.affineOpens => (U : S.Opens))) := by
    simpa only [Subtype.range_coe] using S.isBasis_affineOpens
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hBasis fun U =>
    isIso_app_of_isIso_appTop f U.2
  change IsIso ((TopCat.Sheaf.forget CommRingCat (S : TopCat)).map φ)
  infer_instance

namespace Scheme.Hom

/-- Over an affine base, the canonical normalization of a universally closed
qcqs morphism has the same structure sheaf as the pushforward of the source. -/
lemma isIso_toNormalization_c_of_universallyClosed
    [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f] [IsAffine S] :
    IsIso f.toNormalization.c :=
  isIso_c_of_isIso_appTop f.toNormalization

end Scheme.Hom

end AlgebraicGeometry
