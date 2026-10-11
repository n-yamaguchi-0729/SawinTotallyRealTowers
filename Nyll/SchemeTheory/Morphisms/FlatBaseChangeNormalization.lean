/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ProperNormalization
import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization

/-!
# Flat affine base change for a universally closed normalization

The relative normalization of a universally closed qcqs morphism agrees
with affinization over an affine base. The flat base-change theorem for
sections therefore gives the cartesian square for the native normalization
maps. No connected-fibre or finite-etale hypothesis is used.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
variable [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f]
variable [IsAffine S] [IsAffine T]

/-- Compatibility of the actual normalization comparison with the affine
identifications coming from global sections. -/
lemma normalizationPullback_fst_normalizationIsoSpec :
    (f.normalizationPullback g ≫ pullback.fst f.fromNormalization g) ≫
        f.normalizationIsoSpec.hom =
      (pullback.snd f g).normalizationIsoSpec.hom ≫
        Spec.map (pullback.fst f g).appTop := by
  apply ext_of_isAffine
  rw [← cancel_mono (pullback.snd f g).toNormalization.appTop,
    ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
  apply congrArg Scheme.Hom.appTop
  simp only [Category.assoc, toNormalization_normalizationPullback_fst_assoc,
    toNormalization_normalizationIsoSpec_hom_assoc,
    toNormalization_normalizationIsoSpec_hom]
  exact Scheme.toSpecΓ_naturality (pullback.fst f g)

variable [Flat g]

/-- The canonical first morphism of relative normalization commutes with flat
base change between affine bases for universally closed qcqs morphisms. -/
lemma isPullback_toNormalization_of_flat :
    IsPullback (pullback.snd f g).toNormalization (pullback.fst f g)
      (f.normalizationPullback g ≫ pullback.fst f.fromNormalization g)
      f.toNormalization := by
  refine (isPullback_toSpecΓ_of_flat f g).of_iso
    (Iso.refl _) (pullback.snd f g).normalizationIsoSpec.symm
    (Iso.refl _) f.normalizationIsoSpec.symm ?_ ?_ ?_ ?_
  · change (pullback f g).toSpecΓ ≫
        (pullback.snd f g).normalizationIsoSpec.inv =
      𝟙 _ ≫ (pullback.snd f g).toNormalization
    rw [Category.id_comp,
      ← (pullback.snd f g).toNormalization_normalizationIsoSpec_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm
  · change Spec.map (pullback.fst f g).appTop ≫ f.normalizationIsoSpec.inv =
      (pullback.snd f g).normalizationIsoSpec.inv ≫
        (f.normalizationPullback g ≫ pullback.fst f.fromNormalization g)
    rw [← cancel_epi (pullback.snd f g).normalizationIsoSpec.hom,
      Iso.hom_inv_id_assoc, ← Category.assoc,
      ← f.normalizationPullback_fst_normalizationIsoSpec g,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · change X.toSpecΓ ≫ f.normalizationIsoSpec.inv = 𝟙 _ ≫ f.toNormalization
    rw [Category.id_comp, ← f.toNormalization_normalizationIsoSpec_hom,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Hom
