/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Geometry
import Nyll.SchemeTheory.FiniteEtale.SectionsDescent
import Nyll.SchemeTheory.Affine.AffinizationDescent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Finite étale extension by affinization

A finite étale cover of an open subscheme is the restriction of its
affinization once that affinization is an open immersion and its section
algebra is finite étale. Density of the canonical affinization and properness
of the comparison with the restricted finite cover prove surjectivity.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Finite étale sections and an open affinization produce an actual
extension of a finite étale cover across the ambient affine scheme. -/
theorem exists_finiteEtale_extension_of_open_affinization
    {S W : Scheme.{u}} [IsAffine S] [CompactSpace W]
    (U : S.Opens) (f : W ⟶ U) [IsFiniteEtale f]
    [IsOpenImmersion W.toSpecΓ]
    (h : (f ≫ U.ι).appTop.hom.FiniteEtale) :
    ∃ V : FiniteEtale S,
      Nonempty ((FiniteEtale.pullback U.ι).obj V ≅ FiniteEtale.mk f) := by
  let p : Spec Γ(W, ⊤) ⟶ S := Spec.map (f ≫ U.ι).appTop ≫ S.isoSpec.inv
  let : IsFiniteEtale (Spec.map (f ≫ U.ι).appTop) :=
    IsFiniteEtale.SpecMap_iff.mpr h
  let : IsFiniteEtale S.isoSpec.inv := ⟨⟩
  let : IsFiniteEtale p := inferInstanceAs
    (IsFiniteEtale (Spec.map (f ≫ U.ι).appTop ≫ S.isoSpec.inv))
  have hcomm : W.toSpecΓ ≫ p = f ≫ U.ι := by
    dsimp only [p]
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality]
    change ((f ≫ U.ι) ≫ S.isoSpec.hom) ≫ S.isoSpec.inv = _
    rw [Category.assoc, S.isoSpec.hom_inv_id, Category.comp_id]
  let c : W ⟶ pullback p U.ι := pullback.lift W.toSpecΓ f hcomm
  have hc₁ : c ≫ pullback.fst p U.ι = W.toSpecΓ := pullback.lift_fst _ _ _
  have hc₂ : c ≫ pullback.snd p U.ι = f := pullback.lift_snd _ _ _
  let : IsOpenImmersion (c ≫ pullback.fst p U.ι) := hc₁.symm ▸ inferInstance
  let : IsOpenImmersion c := IsOpenImmersion.of_comp c (pullback.fst p U.ι)
  let : IsFinite (c ≫ pullback.snd p U.ι) := hc₂.symm ▸ inferInstance
  let : IsFinite c := IsFinite.of_comp c (pullback.snd p U.ι)
  let : QuasiCompact W.toSpecΓ := (quasiCompact_iff_compactSpace W.toSpecΓ).mpr
    inferInstance
  let : IsSchemeTheoreticallyDominant W.toSpecΓ := ⟨W.ker_toSpecΓ⟩
  let : IsDominant (c ≫ pullback.fst p U.ι) := hc₁.symm ▸ inferInstance
  let : IsDominant c := IsDominant.of_comp_of_isOpenImmersion c (pullback.fst p U.ι)
  let : Surjective c := surjective_of_isDominant_of_isClosed_range c
    c.isClosedMap.isClosed_range
  let : IsIso c := (isIso_iff_isOpenImmersion_and_surjective c).mpr
    ⟨inferInstance, inferInstance⟩
  let eC : W ≅ pullback p U.ι := asIso c
  refine ⟨FiniteEtale.mk p, ⟨?_⟩⟩
  have e : FiniteEtale.mk f ≅ (FiniteEtale.pullback U.ι).obj (FiniteEtale.mk p) :=
    MorphismProperty.Over.isoMk (P := @IsFiniteEtale)
      (Q := (⊤ : MorphismProperty Scheme.{u})) eC hc₂
  exact e.symm

/-- An extension after affine faithfully flat base change descends when
the extending open immersion preserves global sections. -/
theorem exists_finiteEtale_extension_of_flat_baseChange
    {S T W V : Scheme.{u}} [IsAffine S] [IsAffine T] [CompactSpace W]
    (U : S.Opens) [QuasiCompact U.ι]
    (f : W ⟶ U) [IsFiniteEtale f]
    (g : T ⟶ S) [Flat g] [Surjective g]
    (p : V ⟶ T) [IsFiniteEtale p]
    (j : pullback (f ≫ U.ι) g ⟶ V) [IsOpenImmersion j] [IsIso j.appTop]
    (hj : j ≫ p = pullback.snd (f ≫ U.ι) g) :
    ∃ Z : FiniteEtale S,
      Nonempty ((FiniteEtale.pullback U.ι).obj Z ≅ FiniteEtale.mk f) := by
  let : IsAffine V := isAffine_of_isAffineHom p
  let : IsOpenImmersion
      ((pullback (f ≫ U.ι) g).toSpecΓ ≫ Spec.map j.appTop) := by
    rw [← Scheme.toSpecΓ_naturality]
    infer_instance
  let : IsOpenImmersion (pullback (f ≫ U.ι) g).toSpecΓ :=
    IsOpenImmersion.of_comp _ (Spec.map j.appTop)
  let : IsOpenImmersion W.toSpecΓ :=
    isOpenImmersion_toSpecΓ_of_flat_baseChange (f ≫ U.ι) g
  have hpΓ : p.appTop.hom.FiniteEtale :=
    ((HasAffineProperty.iff_of_isAffine (P := @IsFiniteEtale)
      (Q := affineAnd RingHom.FiniteEtale) (f := p)).mp inferInstance).2
  let : IsFiniteEtale (Spec.map p.appTop) := IsFiniteEtale.SpecMap_iff.mpr hpΓ
  let : IsFiniteEtale (Spec.map j.appTop) := ⟨⟩
  have hsΓ : (pullback.snd (f ≫ U.ι) g).appTop.hom.FiniteEtale := by
    rw [← hj, Scheme.Hom.comp_appTop]
    apply IsFiniteEtale.SpecMap_iff.mp
    rw [Spec.map_comp]
    infer_instance
  exact exists_finiteEtale_extension_of_open_affinization U f
    (finiteEtale_appTop_of_flat_baseChange (f ≫ U.ι) g hsΓ)

end AlgebraicGeometry
