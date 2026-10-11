/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.AffineNormalizationPushforward

/-!
# The structure-sheaf pushforward of relative normalization

The section isomorphisms above affine opens of the original base imply
the full structure-sheaf pushforward assertion for the native relative
normalization, with no affine or Noetherian hypothesis on the base.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u v

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- A qcqs morphism whose section maps are isomorphisms on an affine open
cover induces an isomorphism of the structure sheaf with its pushforward. -/
lemma isIso_c_of_isIso_app_affine_cover [QuasiCompact f] [QuasiSeparated f]
    {I : Type v} (U : I → S.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hCover : iSup U = ⊤) (hSections : ∀ i, IsIso (f.app (U i))) :
    IsIso f.c := by
  let B : (Σ i, (U i).toScheme.affineOpens) → S.Opens :=
    fun j => (U j.1).ι ''ᵁ (j.2 : (U j.1).toScheme.Opens)
  have hBasis : Opens.IsBasis (Set.range B) := by
    rw [Opens.isBasis_iff_nbhd]
    intro W x hx
    have hxCover : x ∈ iSup U := by
      rw [hCover]
      exact Set.mem_univ x
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxCover
    let y : (U i).toScheme := ⟨x, hxi⟩
    have hy : y ∈ (U i).ι ⁻¹ᵁ W := hx
    obtain ⟨V, hV, hyV, hVW⟩ :=
      Opens.isBasis_iff_nbhd.mp (U i).toScheme.isBasis_affineOpens hy
    refine ⟨(U i).ι ''ᵁ V, ⟨⟨i, ⟨V, hV⟩⟩, rfl⟩, ?_, ?_⟩
    · exact ⟨y, hyV, rfl⟩
    · exact ((U i).ι.image_mono hVW).trans ((U i).ι.image_preimage_le W)
  let φ : S.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat f.base).obj X.sheaf :=
    ⟨f.c⟩
  have hBasisSections (j : Σ i, (U i).toScheme.affineOpens) :
      IsIso (φ.hom.app (.op (B j))) := by
    obtain ⟨i, V, hV⟩ := j
    have : IsAffine (U i).toScheme := hU i
    have hComparison := MorphismProperty.arrow_mk_iso_iff
      (MorphismProperty.isomorphisms CommRingCat)
      (arrowResLEAppIso f (U i) (f ⁻¹ᵁ U i) le_rfl)
    change IsIso (f.resLE (U i) (f ⁻¹ᵁ U i) le_rfl).appTop ↔
      IsIso (f.appLE (U i) (f ⁻¹ᵁ U i) le_rfl) at hComparison
    rw [Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.appLE_eq_app] at hComparison
    have : IsIso (f ∣_ U i).appTop := hComparison.mpr (hSections i)
    have hVSections := isIso_app_of_isIso_appTop (f ∣_ U i) hV
    rw [morphismRestrict_app] at hVSections
    let eRestrict : Γ(X, f ⁻¹ᵁ ((U i).ι ''ᵁ V)) ≅
        Γ(X, (f ⁻¹ᵁ U i).ι ''ᵁ ((f ∣_ U i) ⁻¹ᵁ V)) :=
      X.presheaf.mapIso (eqToIso (image_morphismRestrict_preimage f (U i) V)).op
    have : IsIso eRestrict.hom := eRestrict.isIso_hom
    change IsIso (f.app ((U i).ι ''ᵁ V))
    exact (isIso_comp_right_iff (f.app ((U i).ι ''ᵁ V)) eRestrict.hom).mp hVSections
  have : IsIso φ := TopCat.Sheaf.isIso_iff_isIso_basis hBasis hBasisSections
  change IsIso ((TopCat.Sheaf.forget CommRingCat (S : TopCat)).map φ)
  infer_instance

namespace Scheme.Hom

/-- The structure sheaf of the native relative normalization is the pushforward
of the source's structure sheaf for a universally closed qcqs morphism. -/
lemma isIso_toNormalization_c [QuasiCompact f] [QuasiSeparated f]
    [UniversallyClosed f] : IsIso f.toNormalization.c := by
  apply isIso_c_of_isIso_app_affine_cover f.toNormalization
    (fun U : S.affineOpens => f.fromNormalization ⁻¹ᵁ U.1)
    (fun U => U.2.preimage f.fromNormalization)
  · exact TopologicalSpace.IsOpenCover.comap (iSup_affineOpens_eq_top S)
      f.fromNormalization.base.hom
  · intro U
    exact f.isIso_toNormalization_app_of_universallyClosed U.2

end Scheme.Hom

end AlgebraicGeometry
