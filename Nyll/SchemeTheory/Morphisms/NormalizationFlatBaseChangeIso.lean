/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ProperNormalization
import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization

/-!
# The native normalization comparison under flat affine base change

For a universally closed qcqs morphism, the native normalization comparison
is an isomorphism after flat base change between affine bases. The proof
compares the two actual pushout squares on global sections, using the
section isomorphisms of the normalization maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
variable [QuasiCompact f] [QuasiSeparated f] [UniversallyClosed f]
variable [IsAffine S] [IsAffine T] [Flat g]

/-- The actual map from the normalization of the base change to the base change
of the normalization is an isomorphism for flat affine base change. -/
lemma isIso_normalizationPullback_of_flat_affine :
    IsIso (f.normalizationPullback g) := by
  let p : (pullback.snd f g).normalization ⟶ pullback f.fromNormalization g :=
    f.normalizationPullback g
  have hPushout := isPushout_appTop_of_flat f.fromNormalization g
  have hTransport : IsPushout f.fromNormalization.appTop g.appTop
      ((pullback.fst f.fromNormalization g).appTop ≫ p.appTop)
      ((pullback.snd f.fromNormalization g).appTop ≫ p.appTop) := by
    refine (isPushout_appTop_of_flat f g).of_iso'
      (Iso.refl _) (asIso f.toNormalization.appTop)
      (Iso.refl _) (asIso (pullback.snd f g).toNormalization.appTop)
      ?_ ?_ ?_ ?_
    · change 𝟙 _ ≫ f.appTop = f.fromNormalization.appTop ≫ f.toNormalization.appTop
      rw [Category.id_comp, ← Scheme.Hom.comp_appTop, f.toNormalization_fromNormalization]
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · change f.toNormalization.appTop ≫ (pullback.fst f g).appTop =
        ((pullback.fst f.fromNormalization g).appTop ≫ p.appTop) ≫
          (pullback.snd f g).toNormalization.appTop
      simp only [← Scheme.Hom.comp_appTop]
      exact congrArg Scheme.Hom.appTop
        (f.toNormalization_normalizationPullback_fst g).symm
    · change 𝟙 _ ≫ (pullback.snd f g).appTop =
        ((pullback.snd f.fromNormalization g).appTop ≫ p.appTop) ≫
          (pullback.snd f g).toNormalization.appTop
      simp only [Category.id_comp, ← Scheme.Hom.comp_appTop]
      change (pullback.snd f g).appTop =
        ((pullback.snd f g).toNormalization ≫ f.normalizationPullback g ≫
          pullback.snd f.fromNormalization g).appTop
      rw [f.normalizationPullback_snd, toNormalization_fromNormalization]
  let e : Γ(pullback f.fromNormalization g, ⊤) ≅
      Γ((pullback.snd f g).normalization, ⊤) :=
    hPushout.isoIsPushout _ _ hTransport
  have hp : p.appTop = e.hom := by
    apply hPushout.hom_ext
    · exact (IsPushout.inl_isoIsPushout_hom
        Γ(f.normalization, ⊤) Γ(T, ⊤) hPushout hTransport).symm
    · exact (IsPushout.inr_isoIsPushout_hom
        Γ(f.normalization, ⊤) Γ(T, ⊤) hPushout hTransport).symm
  have : IsIso p.appTop := by
    rw [hp]
    infer_instance
  have hIso := MorphismProperty.arrow_mk_iso_iff
    (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine p)
  exact hIso.mpr (inferInstanceAs (IsIso (Spec.map p.appTop)))

end AlgebraicGeometry.Scheme.Hom
