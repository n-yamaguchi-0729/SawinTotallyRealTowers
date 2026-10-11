/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.FiniteSeparable

/-!
# A finite normal source is its generic relative normalization

This generalizes the affine integral-closure argument used for finite étale
covers to any finite morphism with normal integral source. It applies at
ramified boundary points as well. The resulting isomorphism is over the
original target, not merely an abstract isomorphism of schemes.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} [IsIntegral Y] [IsNormalIntegral Y]

private local instance fieldSpecQuasiCompact
    {L : Type u} [Field L] {S : Scheme.{u}} (f : Spec (.of L) ⟶ S) :
    QuasiCompact f where
  isCompact_preimage U _ _ := (Set.toFinite (f ⁻¹' U)).isCompact

private noncomputable def finiteNormalGenericDesc
    (f : Y ⟶ X) [IsFinite f] :
    ((Y.genericExtensionMorphism Y.functionField ≫ f)).normalization ⟶ Y := by
  let hIntegral : IsIntegralHom f :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp
      (inferInstance : IsFinite f) |>.1
  exact @Scheme.Hom.normalizationDesc _ _
    ((Y.genericExtensionMorphism Y.functionField ≫ f)) inferInstance inferInstance _
    ((Y.genericExtensionMorphism Y.functionField)) f hIntegral rfl

omit [IsNormalIntegral Y] in
private lemma finiteNormalGenericDesc_comp
    (f : Y ⟶ X) [IsFinite f] :
    finiteNormalGenericDesc f ≫ f =
      ((Y.genericExtensionMorphism Y.functionField ≫ f)).fromNormalization := by
  let hIntegral : IsIntegralHom f :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp
      (inferInstance : IsFinite f) |>.1
  dsimp [finiteNormalGenericDesc]
  exact @Scheme.Hom.normalizationDesc_comp _ _
    ((Y.genericExtensionMorphism Y.functionField ≫ f)) inferInstance inferInstance _
    ((Y.genericExtensionMorphism Y.functionField)) f hIntegral rfl

omit [IsNormalIntegral Y] in
private lemma toNormalization_finiteNormalGenericDesc
    (f : Y ⟶ X) [IsFinite f] :
    ((Y.genericExtensionMorphism Y.functionField ≫ f)).toNormalization ≫
        finiteNormalGenericDesc f =
      (Y.genericExtensionMorphism Y.functionField) := by
  let hIntegral : IsIntegralHom f :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp
      (inferInstance : IsFinite f) |>.1
  dsimp [finiteNormalGenericDesc]
  exact @Scheme.Hom.toNormalization_normalizationDesc _ _
    ((Y.genericExtensionMorphism Y.functionField ≫ f)) inferInstance inferInstance _
    ((Y.genericExtensionMorphism Y.functionField)) f hIntegral rfl

private lemma appLE_preimage_eq_app_of_eq {Y Z : Scheme.{u}}
    (g q : Y ⟶ Z) (h : g = q) (U : Z.Opens) :
    g.appLE U (q ⁻¹ᵁ U) (by rw [h]) = q.app U := by
  subst q
  exact g.appLE_eq_app

/-- The canonical map from the generic relative normalization to a finite
normal integral source is an isomorphism. -/
theorem finiteNormalGenericDesc_isIso
    (f : Y ⟶ X) [IsFinite f] :
    IsIso (finiteNormalGenericDesc f) := by
  let : IsIntegralHom f :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType f).mp
      (inferInstance : IsFinite f) |>.1
  let : IsAffineHom f := (inferInstance : IsAffineHom f)
  let L : Type u := Y.functionField
  let : CommRing L :=
    CommRingCat.instCommRingObjForgetRingHomCarrier
  let q : Spec (.of L) ⟶ Y := (Y.genericExtensionMorphism Y.functionField)
  let genericComposite : Spec (.of L) ⟶ X := (Y.genericExtensionMorphism Y.functionField ≫ f)
  let d : genericComposite.normalization ⟶ Y :=
    finiteNormalGenericDesc f
  let : IsIntegralHom d := by
    apply (IsIntegralHom.comp_iff (f := d) (g := f)).mp
    rw [show d ≫ f = genericComposite.fromNormalization from
      finiteNormalGenericDesc_comp f]
    infer_instance
  let : IsAffineHom d := inferInstance
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme.{u})
  intro y
  obtain ⟨U, hU, hyU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤)
      (x := f y) (by trivial)
  let V : Y.Opens := f ⁻¹ᵁ U
  have hyV : y ∈ V := hyU
  have hV : IsAffineOpen V :=
    @IsAffineOpen.preimage _ _ U hU f
      (inferInstance : IsAffineHom f)
  let : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, hyV,
    (isIso_morphismRestrict_iff_isIso_app d hV).mpr ?_⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  let A : Type u := Γ(X, U)
  let T : Type u := Γ(Y, V)
  let S : Type u := Γ(Spec (.of L), genericComposite ⁻¹ᵁ U)
  let : Algebra A T := (f.app U).hom.toAlgebra
  let : Algebra T L := Y.affineExtensionAlgebra V L
  let : Algebra A L :=
    ((algebraMap T L).comp (algebraMap A T)).toAlgebra
  let : IsScalarTower A T L := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra A S := (genericComposite.app U).hom.toAlgebra
  let C : Type u := integralClosure A S
  have hpre : d ⁻¹ᵁ V = genericComposite.fromNormalization ⁻¹ᵁ U := by
    dsimp only [d, V]
    rw [← Scheme.Hom.comp_preimage,
      finiteNormalGenericDesc_comp]
  let eN : Γ(genericComposite.normalization, d ⁻¹ᵁ V) ≅ .of C :=
    genericComposite.normalization.presheaf.mapIso (eqToIso hpre.symm).op ≪≫
      genericComposite.normalizationObjIso hU
  have hqpre : q ⁻¹ᵁ V = genericComposite ⁻¹ᵁ U := by
    dsimp only [q, genericComposite, V]
    simp only [Scheme.Hom.comp_preimage]
  cases hqpre
  let : Algebra T Γ(Spec (.of L), q ⁻¹ᵁ V) :=
    (q.app V).hom.toAlgebra
  let : Algebra A Γ(Spec (.of L), q ⁻¹ᵁ V) :=
    ((algebraMap T Γ(Spec (.of L), q ⁻¹ᵁ V)).comp
      (algebraMap A T)).toAlgebra
  let : IsScalarTower A T Γ(Spec (.of L), q ⁻¹ᵁ V) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let eS0 : Γ(Spec (.of L), q ⁻¹ᵁ V) ≃ₐ[T] L :=
    Y.genericExtensionSectionsAlgEquiv L V
  let eS : S ≃ₐ[A] L := by
    let eEq : S ≃ₐ[A] Γ(Spec (.of L), q ⁻¹ᵁ V) := by
      exact AlgEquiv.refl
    exact eEq.trans (eS0.restrictScalars A)
  let eC : C ≃ₐ[A] integralClosure A L := eS.mapIntegralClosure
  let : IsIntegrallyClosed T :=
    IsNormalIntegral.affine_isIntegrallyClosed V hV
  let : IsFractionRing T L :=
    functionField_isFractionRing_of_isAffineOpen Y V hV
  let : Algebra.IsIntegral A T := by
    refine ⟨?_⟩
    intro t
    exact ((inferInstance : IsIntegralHom f).isIntegral_app U hU) t
  let : IsIntegralClosure T A L := inferInstance
  let eT : T ≃ₐ[A] integralClosure A L :=
    IsIntegralClosure.equiv A T L (integralClosure A L)
  have hcomp :
      (d.app V ≫ eN.hom ≫ eC.toRingEquiv.toCommRingCatIso.hom) =
        eT.toRingEquiv.toCommRingCatIso.hom := by
    apply CommRingCat.hom_ext
    ext t
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_ofHom]
    change algebraMap (integralClosure A L) L
        (eC (eN.hom (d.app V t))) =
      algebraMap (integralClosure A L) L (eT t)
    rw [IsIntegralClosure.algebraMap_equiv]
    change eS ((eN.hom (d.app V t) : C) : S) = algebraMap T L t
    have hdq : d.app V ≫ eN.hom ≫
        CommRingCat.ofHom (Subalgebra.val (integralClosure A S)).toRingHom =
          q.app V := by
      have hle : genericComposite ⁻¹ᵁ U ≤
          genericComposite.toNormalization ⁻¹ᵁ (genericComposite.fromNormalization ⁻¹ᵁ U) := by
        rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]
      have hnorm : (genericComposite.normalizationObjIso hU).hom ≫
          CommRingCat.ofHom
            (Subalgebra.val (integralClosure A S)).toRingHom =
          genericComposite.toNormalization.appLE (genericComposite.fromNormalization ⁻¹ᵁ U)
            (genericComposite ⁻¹ᵁ U) hle := by
        simpa only [A, S] using genericComposite.normalizationObjIso_hom_val hU
      have hdle : genericComposite.fromNormalization ⁻¹ᵁ U ≤ d ⁻¹ᵁ V := by
        rw [hpre]
      have htransport : d.app V ≫
          (genericComposite.normalization.presheaf.mapIso
            (eqToIso hpre.symm).op).hom =
          d.appLE V (genericComposite.fromNormalization ⁻¹ᵁ U) hdle := by
        rw [d.app_eq_appLE]
        exact d.appLE_map' hdle hpre.symm
      have hqd : genericComposite.toNormalization ≫ d = q := by
        exact toNormalization_finiteNormalGenericDesc f
      dsimp only [eN]
      simp only [Iso.trans_hom, Category.assoc]
      rw [hnorm]
      rw [← Category.assoc, htransport,
        Scheme.Hom.appLE_comp_appLE]
      exact appLE_preimage_eq_app_of_eq
        (genericComposite.toNormalization ≫ d) q hqd V
    have hdq_t := congrArg (fun k ↦ k.hom t) hdq
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom,
      RingHom.comp_apply] at hdq_t
    change ((eN.hom (d.app V t) : C) : S) = q.app V t at hdq_t
    rw [hdq_t]
    exact Y.genericExtensionSectionsIso_hom_app L V t
  have : IsIso
      (d.app V ≫ eN.hom ≫ eC.toRingEquiv.toCommRingCatIso.hom) := by
    rw [hcomp]
    infer_instance
  have : IsIso (eN.hom ≫ eC.toRingEquiv.toCommRingCatIso.hom) :=
    inferInstance
  let : IsIso (d.app V) :=
    IsIso.of_isIso_comp_right (d.app V)
      (eN.hom ≫ eC.toRingEquiv.toCommRingCatIso.hom)
  exact ConcreteCategory.bijective_of_isIso _

/-- A finite normal integral source is its generic relative normalization. -/
noncomputable def finiteNormalGenericIso
    (f : Y ⟶ X) [IsFinite f] :
    ((Y.genericExtensionMorphism Y.functionField ≫ f)).normalization ≅ Y :=
  letI := finiteNormalGenericDesc_isIso f
  asIso (finiteNormalGenericDesc f)

/-- The generic normalization isomorphism commutes with the original finite map. -/
@[reassoc (attr := simp)]
theorem finiteNormalGenericIso_inv_fromNormalization
    (f : Y ⟶ X) [IsFinite f] :
    (finiteNormalGenericIso f).inv ≫
        ((Y.genericExtensionMorphism Y.functionField ≫ f)).fromNormalization =
      f := by
  rw [← finiteNormalGenericDesc_comp f]
  change (finiteNormalGenericIso f).inv ≫
      (finiteNormalGenericIso f).hom ≫ f = f
  exact Iso.inv_hom_id_assoc _ _


end AlgebraicGeometry.Scheme.Hom
