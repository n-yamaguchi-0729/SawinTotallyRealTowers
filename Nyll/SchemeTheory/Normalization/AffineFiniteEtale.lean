/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.Affine
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.Etale.AffineBaseChangeProperties
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The structure map of an affine relative normalization

The canonical affine normalization isomorphism intertwines the actual
structure map with the algebra map into the integral closure. This gives
the ring criterion for finite etaleness of that actual normalization map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable (R T : Type u) [CommRing R] [CommRing T] [Algebra R T]

/-- The affine normalization comparison is an isomorphism over the original
base, for the literal structural algebra map. -/
@[reassoc]
theorem specNormalizationIso_hom_fromNormalization :
    (specNormalizationIso R T).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R T))) =
      (affineStructureMap R T).fromNormalization := by
  apply spec_toNormalization_hom_ext R T
  rw [← Category.assoc, toNormalization_specNormalizationIso_hom,
    ← Spec.map_comp, Scheme.Hom.toNormalization_fromNormalization]
  rfl

/-- Finite etaleness of an affine relative normalization is precisely finite
etaleness of the literal integral-closure algebra. -/
theorem isFiniteEtale_specNormalization_iff :
    IsFiniteEtale (affineStructureMap R T).fromNormalization ↔
      Module.Finite R (integralClosure R T) ∧ Algebra.Etale R (integralClosure R T) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R T)))
  let e := specNormalizationIso R T
  have hg : g = e.inv ≫ (affineStructureMap R T).fromNormalization := by
    rw [← specNormalizationIso_hom_fromNormalization R T, Iso.inv_hom_id_assoc]
  constructor
  · intro h
    let : IsFinite (affineStructureMap R T).fromNormalization := h.toIsFinite
    let : Etale (affineStructureMap R T).fromNormalization := h.toEtale
    have hf : IsFinite g := by
      rw [hg]
      infer_instance
    have he : Etale g := by
      rw [hg]
      infer_instance
    exact ⟨RingHom.finite_algebraMap.mp (IsFinite.SpecMap_iff _ |>.mp hf),
      RingHom.etale_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Etale)).mp he)⟩
  · rintro ⟨hfinite, hetale⟩
    let : IsFinite g := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
    let : Etale g := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr hetale)
    have hcomp : IsFiniteEtale (e.hom ≫ g) := ⟨⟩
    exact specNormalizationIso_hom_fromNormalization R T ▸ hcomp

/-- Finite etaleness of an actual base change of an affine normalization
supplies the canonical tensor-algebra properties used in affine spreading. -/
theorem finite_etale_tensor_integralClosure_of_normalization_baseChange
    (A : Type u) [CommRing A] [Algebra R A]
    (h : IsFiniteEtale (pullback.snd (affineStructureMap R T).fromNormalization
      (Spec.map (CommRingCat.ofHom (algebraMap R A))))) :
    Module.Finite A (A ⊗[R] integralClosure R T) ∧
      Algebra.Etale A (A ⊗[R] integralClosure R T) := by
  let f := (affineStructureMap R T).fromNormalization
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R T)))
  let b := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let e := specNormalizationIso R T
  have he : f ≫ 𝟙 _ = e.hom ≫ g :=
    (Category.comp_id f).trans (specNormalizationIso_hom_fromNormalization R T).symm
  let l := pullback.map f b g b e.hom (𝟙 _) (𝟙 _) he
    ((Category.comp_id b).trans (Category.id_comp b).symm)
  have hl : l ≫ pullback.snd g b = pullback.snd f b := by
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hcomp : IsFiniteEtale (l ≫ pullback.snd g b) := hl.symm ▸ h
  let : IsFinite (l ≫ pullback.snd g b) := hcomp.toIsFinite
  let : Etale (l ≫ pullback.snd g b) := hcomp.toEtale
  have hginv : IsFiniteEtale (inv l ≫ (l ≫ pullback.snd g b)) := ⟨⟩
  have hg : IsFiniteEtale (pullback.snd g b) :=
    IsIso.inv_hom_id_assoc l (pullback.snd g b) ▸ hginv
  exact ⟨SchemeTheory.tensorProduct_finite_of_spec_baseChange R A
      (integralClosure R T) hg.toIsFinite,
    SchemeTheory.tensorProduct_etale_of_spec_baseChange R A
      (integralClosure R T) hg.toEtale⟩

end AlgebraicGeometry
