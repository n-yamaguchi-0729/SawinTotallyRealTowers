/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.Quotient
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteAbelianClassification
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicDegreeOnNumberField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitNormQuotient
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassNormTopology
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityTransport
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisPresentation

/-!
# Reciprocity on the standard number-field formation

The finite norm-residue symbol uses the normalized cyclotomic degree and the
valuation of the actual standard class representation over the original base.
The quotient target is the abelianization of the automorphism group of the
two concrete fixed fields.
-/

@[expose] public section

open scoped IsMulCommutative NumberField
open ClassFormation CyclicCohomology KummerTheory LocalClassFieldTheory

namespace GlobalClassFieldTheory.Reciprocity

universe u v

variable (K : Type u) [Field K] [NumberField K]

attribute [local instance] abstractRelativeFixedFieldNumberField

section FixedFieldNormSubgroups

variable (H : FiniteAbstractField Gal(SeparableClosure K/K))

local notation "K₀" => abstractFixedField K (SeparableClosure K) H.field

local instance fixedFieldNormBaseFiniteDimensional : FiniteDimensional K K₀ :=
  abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite

/-- The norm subgroup on the standard idèle classes of the actual lower fixed field. -/
noncomputable def standardFixedFieldAbelianNormSubgroup (L : FiniteAbelianSubextension H.field) :
    AddSubgroup (Additive (NumberField.IdeleClassGroup (𝓞 K₀) K₀)) :=
  let T := L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension (K := H)
  let : FiniteDimensional K (abstractFixedField K (SeparableClosure K) L.field) :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) L.field T.field.finite
  (NumberField.IdeleClassGroup.norm K₀
    (abstractRelativeFixedField K (SeparableClosure K) L.below)).range.toAddSubgroup

/-- The fixed-part comparison takes the abstract norm to the determinant norm
of the same extension on standard idèle classes. -/
theorem standardFixedFieldAbelianNormSubgroup_eq_map (L : FiniteAbelianSubextension H.field) :
    standardFixedFieldAbelianNormSubgroup K H L =
      (L.normSubgroup (ideleClassRepresentation K)).map
        (abstractFixedFieldIdeleClassEquivFixed K H.field).symm.toAddMonoidHom := by
  let T := L.toFiniteGaloisExtension.toFiniteAbstractFieldExtension (K := H)
  let : FiniteDimensional K (abstractFixedField K (SeparableClosure K) L.field) :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) L.field T.field.finite
  let : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field L.field L.below) := L.finite
  exact (map_finiteNormSubgroup_eq_standardIdeleClassNormRange K H.field L.field
    L.below L.normal).symm

/-- Inclusion of the actual abelian subextensions reverses inclusion of their
standard idèle-class norm subgroups. -/
theorem le_iff_standardFixedFieldAbelianNormSubgroup_le
    (L₁ L₂ : FiniteAbelianSubextension H.field) :
    L₁ ≤ L₂ ↔
      standardFixedFieldAbelianNormSubgroup K H L₂ ≤
        standardFixedFieldAbelianNormSubgroup K H L₁ := by
  rw [standardFixedFieldAbelianNormSubgroup_eq_map K H L₂,
    standardFixedFieldAbelianNormSubgroup_eq_map K H L₁]
  exact (FiniteAbelianSubextension.le_iff_normSubgroup_le
    (numberFieldCyclotomicIdeleClassValuationData K)
    (ideleClassRepresentation_satisfiesClassFieldAxiom K) H L₁ L₂).trans
    (AddSubgroup.map_le_map_iff_of_injective
      (abstractFixedFieldIdeleClassEquivFixed K H.field).symm.injective).symm

end FixedFieldNormSubgroups

/-- The actual finite norm-residue map on standard fixed-field class quotients. -/
noncomputable def standardFixedFieldNormResidueEquiv
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) (J : FiniteGaloisSubextension H.field)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J.field)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let E := abstractRelativeFixedField K (SeparableClosure K) J.below
    let n := NumberField.IdeleClassGroup.norm F E
    (NumberField.IdeleClassGroup (𝓞 F) F ⧸ n.range) ≃* Group.Abelianization Gal(E/F) := by
  intro F E n
  let : Finite (H.field.toSubgroup ⧸ (J.field.toSubgroup.subgroupOf H.field.toSubgroup)) := J.finite
  let eClass :=
    finiteNormQuotientEquivStandardIdeleClassNormQuotient K H.field J.field J.below J.normal
  let eGal := J.extensionQuotientMulEquiv.trans
    (abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K) H.field J.field
      J.below J.normal)
  let eRec := (numberFieldCyclotomicDegreeData K).normResidueSymbol
    (ideleClassRepresentation K) (numberFieldCyclotomicIdeleClassValuationData K)
    (ideleClassRepresentation_satisfiesClassFieldAxiom K) H J
  exact MulEquiv.toAdditive.symm
    (eClass.symm.trans (eRec.trans (MulEquiv.toAdditive (MulEquiv.abelianizationCongr eGal))))

/-- The finite Artin map evaluates the norm-residue equivalence on the original class. -/
noncomputable def standardFixedFieldArtin
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) (J : FiniteGaloisSubextension H.field)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J.field)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let E := abstractRelativeFixedField K (SeparableClosure K) J.below
    NumberField.IdeleClassGroup (𝓞 F) F →* Group.Abelianization Gal(E/F) := by
  intro F E
  let n := NumberField.IdeleClassGroup.norm F E
  exact (standardFixedFieldNormResidueEquiv K H J).toMonoidHom.comp (QuotientGroup.mk' n.range)

private theorem normResidue_quotient_ker
    {A B : Type*} [Group A] [Group B]
    (N : Subgroup A) [N.Normal] (e : A ⧸ N ≃* B) :
    (e.toMonoidHom.comp (QuotientGroup.mk' N)).ker = N := by
  ext a
  change e (a : A ⧸ N) = 1 ↔ a ∈ N
  exact e.map_eq_one_iff.trans (QuotientGroup.eq_one_iff a)

/-- The Artin map has the range of the same determinant norm as its kernel. -/
theorem standardFixedFieldArtin_ker
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) (J : FiniteGaloisSubextension H.field)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J.field)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    let E := abstractRelativeFixedField K (SeparableClosure K) J.below
    (standardFixedFieldArtin K H J).ker = (NumberField.IdeleClassGroup.norm F E).range := by
  intro F E
  exact normResidue_quotient_ker (NumberField.IdeleClassGroup.norm F E).range
    (standardFixedFieldNormResidueEquiv K H J)

/-- The original standard classes are the fixed coefficients at the
intrinsic base subgroup. -/
noncomputable def standardNumberFieldClassEquivIntrinsicFixed :
    Additive (NumberField.IdeleClassGroup (𝓞 K) K) ≃+
      ambientFixedAddSubgroup (ideleClassRepresentation K)
        (intrinsicFiniteAbstractBase K).field := by
  let e := FunctionField.finiteGaloisBaseFixedFieldEquiv K
  let H := intrinsicFiniteAbstractBase K
  let : FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field) :=
    e.toLinearEquiv.finiteDimensional
  exact (MulEquiv.toAdditive (NumberField.IdeleClassGroup.congr (e.restrictScalars ℚ))).trans
    (abstractFixedFieldIdeleClassEquivFixed K (intrinsicFiniteAbstractBase K).field)

/-- An explicit realization in the separable closure of the original base
identifies the standard norm-residue quotient with the actual finite Galois abelianization. -/
noncomputable def standardNumberFieldNormResidueEquivOfEmbedding
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (NumberField.IdeleClassGroup.norm K L).range) ≃*
      Group.Abelianization Gal(L/K) := by
  let Ω := SeparableClosure K
  let H := intrinsicFiniteAbstractBase K
  let J := finiteGaloisAbstractExtensionOfEmbedding K L i
  let F := abstractFixedField K Ω H.field
  let E₀ := abstractFixedField K Ω J.field
  let E := abstractRelativeFixedField K Ω J.below
  have hE : E₀ = i.fieldRange := InfiniteGalois.fixedField_fixingSubgroup i.fieldRange
  let eK₀ : K ≃ₐ[K] F := FunctionField.finiteGaloisBaseFixedFieldEquiv K
  let eL₀ : L ≃ₐ[K] E₀ := i.equivFieldRange.trans (IntermediateField.equivOfEq hE.symm)
  let : FiniteDimensional K F := eK₀.toLinearEquiv.finiteDimensional
  let : FiniteDimensional K E₀ := eL₀.toLinearEquiv.finiteDimensional
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional K Ω H.field J.field J.below H.finite J.finite
  let eK : K ≃ₐ[ℚ] F := eK₀.restrictScalars ℚ
  let eL : L ≃ₐ[ℚ] E := eL₀.restrictScalars ℚ
  have hSquare (a : K) : eL (algebraMap K L a) = algebraMap F E (eK a) := by
    apply Subtype.ext
    change i (algebraMap K L a) = (eK₀ a : Ω)
    have hK : eK₀ a = algebraMap K F a := eK₀.commutes a
    rw [hK]
    exact i.commutes a
  let eC := QuotientGroup.congr (NumberField.IdeleClassGroup.norm K L).range
    (NumberField.IdeleClassGroup.norm F E).range (NumberField.IdeleClassGroup.congr eK)
    (NumberField.IdeleClassGroup.norm_range_map_congr_of_compatible K L eK eL hSquare)
  let : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) := J.finite
  let eNorm :=
    finiteNormQuotientEquivStandardIdeleClassNormQuotient K H.field J.field J.below J.normal
  let eRec := (numberFieldCyclotomicDegreeData K).normResidueSymbol (ideleClassRepresentation K)
    (numberFieldCyclotomicIdeleClassValuationData K)
    (ideleClassRepresentation_satisfiesClassFieldAxiom K) H J
  let eGal := J.extensionQuotientMulEquiv.trans
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i)
  exact eC.trans (MulEquiv.toAdditive.symm
    (eNorm.symm.trans (eRec.trans (MulEquiv.toAdditive eGal.abelianizationCongr))))

/-- The Artin map on the original standard idele classes, using the chosen
embedding into the original base's separable closure. -/
noncomputable def standardNumberFieldArtin
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    NumberField.IdeleClassGroup (𝓞 K) K →* Group.Abelianization Gal(L/K) :=
  (standardNumberFieldNormResidueEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)).toMonoidHom.comp
      (QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range)

/-- The original Artin map evaluates the actual abstract norm class with
the lower fixed coefficient and the original quotient restriction. -/
theorem standardNumberFieldArtin_finiteNormClass
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    let H := intrinsicFiniteAbstractBase K
    let J := finiteGaloisAbstractExtension K L
    letI : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) := J.finite
    standardNumberFieldArtin K L c =
      (J.extensionQuotientMulEquiv.trans
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
        (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L))).abelianizationCongr
        (((numberFieldCyclotomicDegreeData K).normResidueSymbol (ideleClassRepresentation K)
          (numberFieldCyclotomicIdeleClassValuationData K)
          (ideleClassRepresentation_satisfiesClassFieldAxiom K)
          H J (finiteNormClass (ideleClassRepresentation K) H.field J.field J.below
            (standardNumberFieldClassEquivIntrinsicFixed K (Additive.ofMul c)))).toMul) := by
  intro H J
  let _ : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) := J.finite
  let F := abstractFixedField K (SeparableClosure K) H.field
  let E := abstractRelativeFixedField K (SeparableClosure K) J.below
  let eK := FunctionField.finiteGaloisBaseFixedFieldEquiv K
  let eL := FunctionField.finiteGaloisEmbeddedFixedFieldEquiv K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)
  let : FiniteDimensional K F := eK.toLinearEquiv.finiteDimensional
  let : FiniteDimensional K (abstractFixedField K (SeparableClosure K) J.field) :=
    eL.toLinearEquiv.finiteDimensional
  let n := NumberField.IdeleClassGroup.norm F E
  let eNorm :=
    finiteNormQuotientEquivStandardIdeleClassNormQuotient K H.field J.field J.below J.normal
  let x := standardNumberFieldClassEquivIntrinsicFixed K (Additive.ofMul c)
  let eFixed := abstractFixedFieldIdeleClassEquivFixed K H.field
  let d := Additive.ofMul (NumberField.IdeleClassGroup.congr (eK.restrictScalars ℚ) c)
  let q (a : Additive (NumberField.IdeleClassGroup (𝓞 F) F)) :=
    Additive.ofMul (QuotientGroup.mk' n.range a.toMul)
  let y := finiteNormClass (ideleClassRepresentation K) H.field J.field J.below x
  have hx : eFixed.symm x = d := eFixed.symm_apply_apply d
  have heval : eNorm y = q (eFixed.symm x) :=
    finiteNormQuotientEquivStandardIdeleClassNormQuotient_finiteNormClass
      K H.field J.field J.below J.normal x
  have hClass : eNorm.symm (q d) = y := calc
    eNorm.symm (q d) = eNorm.symm (eNorm y) :=
      congrArg eNorm.symm (heval.trans (congrArg q hx)).symm
    _ = y := eNorm.symm_apply_apply y
  let eGal := J.extensionQuotientMulEquiv.trans
    (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L))
  let eRec := (numberFieldCyclotomicDegreeData K).normResidueSymbol (ideleClassRepresentation K)
    (numberFieldCyclotomicIdeleClassValuationData K)
    (ideleClassRepresentation_satisfiesClassFieldAxiom K) H J
  exact congrArg (fun y => eGal.abelianizationCongr (eRec y).toMul) hClass

/-- The original-field Artin map is surjective. -/
theorem standardNumberFieldArtin_surjective
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Function.Surjective (standardNumberFieldArtin K L) :=
  (standardNumberFieldNormResidueEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)).surjective.comp
      (QuotientGroup.mk'_surjective (NumberField.IdeleClassGroup.norm K L).range)

/-- The original-field Artin map has the range of the actual standard norm as its kernel. -/
theorem standardNumberFieldArtin_ker
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    (standardNumberFieldArtin K L).ker = (NumberField.IdeleClassGroup.norm K L).range := by
  exact normResidue_quotient_ker (NumberField.IdeleClassGroup.norm K L).range
    (standardNumberFieldNormResidueEquivOfEmbedding K L
      (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L))

/-- Finite abelian norm-residue reciprocity in the ordinary topology of the
standard class quotient and the finite Krull topology. -/
noncomputable def standardNumberFieldNormResidueContinuousMulEquiv
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (NumberField.IdeleClassGroup.norm K L).range) ≃ₜ*
      Gal(L/K) := by
  let : DiscreteTopology
      (NumberField.IdeleClassGroup (𝓞 K) K ⧸ (NumberField.IdeleClassGroup.norm K L).range) :=
    QuotientGroup.discreteTopology
      (GlobalClassFields.ideleClassNorm_range_isOpen (K := K) (L := L))
  let e := (standardNumberFieldNormResidueEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L)).trans
      (Group.Abelianization.equivOfComm : Gal(L/K) ≃* Group.Abelianization Gal(L/K)).symm
  exact { e with
    continuous_toFun := continuous_of_discreteTopology
    continuous_invFun := continuous_of_discreteTopology }

/-- The original-field norm-residue map is continuous on standard idele classes. -/
noncomputable def standardNumberFieldArtinContinuousMonoidHom
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    NumberField.IdeleClassGroup (𝓞 K) K →ₜ* Gal(L/K) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (standardNumberFieldNormResidueContinuousMulEquiv K L)).comp
      { QuotientGroup.mk' (NumberField.IdeleClassGroup.norm K L).range with
        continuous_toFun := QuotientGroup.continuous_mk }

/-- Forgetting continuity and identifying the abelianization recovers the same Artin map. -/
@[simp]
theorem standardNumberFieldArtinContinuousMonoidHom_apply
    (L : Type v) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    standardNumberFieldArtinContinuousMonoidHom K L c =
      (Group.Abelianization.equivOfComm : Gal(L/K) ≃* Group.Abelianization Gal(L/K)).symm
        (standardNumberFieldArtin K L c) :=
  rfl

/-- The finite norm subgroup over the original base is the transported range
of the standard determinant norm from its finite Galois fixed field. -/
theorem standardNumberFieldFiniteNormSubgroup
    (J : FiniteGaloisSubextension (baseField Gal(SeparableClosure K/K))) :
    let F := abstractFixedField K (SeparableClosure K) J.field
    letI : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) J.field J.finite
    J.normSubgroup (ideleClassRepresentation K) =
      (NumberField.IdeleClassGroup.norm K F).range.toAddSubgroup.map
        (ideleClassEquivBaseFixed K).toAddMonoidHom := by
  intro F
  let _ : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) J.field J.finite
  let H : FiniteAbstractField Gal(SeparableClosure K/K) := ⟨J.field, J.finite⟩
  let e := ideleClassEquivBaseFixed K
  let eF := abstractFixedFieldIdeleClassEquivFixed K H.field
  let n := NumberField.IdeleClassGroup.norm K F
  let : Finite ((baseField Gal(SeparableClosure K/K)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(SeparableClosure K/K)) H.field (le_baseField H.field)) :=
    J.finite
  change (normToBase (ideleClassRepresentation K) H.field).range =
    n.range.toAddSubgroup.map e.toAddMonoidHom
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := eF.surjective b
    exact ⟨Additive.ofMul (n c.toMul), ⟨c.toMul, rfl⟩,
      (abstractFixedFieldIdeleClassEquivFixed_normToBase K H c.toMul).symm⟩
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨eF (Additive.ofMul c), abstractFixedFieldIdeleClassEquivFixed_normToBase K H c⟩

section BaseNormSubgroups

local notation "B" => baseField Gal(SeparableClosure K/K)
local notation "C" => Additive (NumberField.IdeleClassGroup (𝓞 K) K)
local notation "V" => ambientFixedAddSubgroup (ideleClassRepresentation K) B

/-- The determinant-norm range on the original number field's standard idèle classes. -/
noncomputable def standardNumberFieldAbelianNormSubgroup (L : FiniteAbelianSubextension B) :
    AddSubgroup (Additive (NumberField.IdeleClassGroup (𝓞 K) K)) :=
  let F := abstractFixedField K (SeparableClosure K) L.field
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) L.field L.finite
  (NumberField.IdeleClassGroup.norm K F).range.toAddSubgroup

private theorem standardNumberFieldAbelianNormSubgroup_eq_map (L : FiniteAbelianSubextension B) :
    standardNumberFieldAbelianNormSubgroup K L =
      (L.normSubgroup (ideleClassRepresentation K)).map
        (ideleClassEquivBaseFixed K).symm.toAddMonoidHom := by
  let e := ideleClassEquivBaseFixed K
  let f : V →+ C := e.symm.toAddMonoidHom
  let g : C →+ V := e.toAddMonoidHom
  have h : L.normSubgroup (ideleClassRepresentation K) =
      (standardNumberFieldAbelianNormSubgroup K L).map g :=
    standardNumberFieldFiniteNormSubgroup K L.toFiniteGaloisExtension
  have hcomp : f.comp g = AddMonoidHom.id C := by
    apply AddMonoidHom.ext
    intro a
    exact e.symm_apply_apply a
  change standardNumberFieldAbelianNormSubgroup K L =
    (L.normSubgroup (ideleClassRepresentation K)).map f
  rw [h, AddSubgroup.map_map, hcomp, AddSubgroup.map_id]

/-- The norm range from a compositum is the intersection of the two norm ranges
in the standard idèle-class group of the original number field. -/
theorem standardNumberFieldAbelianNormSubgroup_compositum (L₁ L₂ : FiniteAbelianSubextension B) :
    standardNumberFieldAbelianNormSubgroup K (L₁.compositum L₂) =
      standardNumberFieldAbelianNormSubgroup K L₁ ⊓
        standardNumberFieldAbelianNormSubgroup K L₂ := by
  rw [standardNumberFieldAbelianNormSubgroup_eq_map K (L₁.compositum L₂),
    standardNumberFieldAbelianNormSubgroup_eq_map K L₁,
    standardNumberFieldAbelianNormSubgroup_eq_map K L₂]
  have h : (L₁.compositum L₂).normSubgroup (ideleClassRepresentation K) =
      L₁.normSubgroup (ideleClassRepresentation K) ⊓ L₂.normSubgroup (ideleClassRepresentation K) :=
    FiniteAbelianSubextension.normSubgroup_compositum
      (numberFieldCyclotomicIdeleClassValuationData K)
      (ideleClassRepresentation_satisfiesClassFieldAxiom K)
      (FiniteAbstractField.base Gal(SeparableClosure K/K)) L₁ L₂
  rw [h]
  apply AddSubgroup.map_inf
  exact (ideleClassEquivBaseFixed K).symm.injective

/-- The norm range from an intersection field is the product of the two norm ranges
in the standard idèle-class group of the original number field. -/
theorem standardNumberFieldAbelianNormSubgroup_intersection (L₁ L₂ : FiniteAbelianSubextension B) :
    standardNumberFieldAbelianNormSubgroup K (L₁.intersection L₂) =
      standardNumberFieldAbelianNormSubgroup K L₁ ⊔
        standardNumberFieldAbelianNormSubgroup K L₂ := by
  rw [standardNumberFieldAbelianNormSubgroup_eq_map K (L₁.intersection L₂),
    standardNumberFieldAbelianNormSubgroup_eq_map K L₁,
    standardNumberFieldAbelianNormSubgroup_eq_map K L₂]
  have h : (L₁.intersection L₂).normSubgroup (ideleClassRepresentation K) =
      L₁.normSubgroup (ideleClassRepresentation K) ⊔ L₂.normSubgroup (ideleClassRepresentation K) :=
    FiniteAbelianSubextension.normSubgroup_intersection
      (numberFieldCyclotomicIdeleClassValuationData K)
      (ideleClassRepresentation_satisfiesClassFieldAxiom K)
      (FiniteAbstractField.base Gal(SeparableClosure K/K)) L₁ L₂
  rw [h]
  apply AddSubgroup.map_sup

end BaseNormSubgroups

private theorem addSubgroup_eq_of_equiv_map_eq
    {A B : Type*} [AddGroup A] [AddGroup B] (e : A ≃+ B) (P Q : AddSubgroup A)
    (h : P.map e.toAddMonoidHom = Q.map e.toAddMonoidHom) : P = Q :=
  AddSubgroup.map_injective (f := e.toAddMonoidHom) e.injective h

/-- The finite Galois extension determined by an embedding in the original
separable closure, over the distinguished abstract base. -/
noncomputable def standardNumberFieldGaloisSubextensionOfEmbedding
    (L : Type v) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteGaloisSubextension (baseField Gal(SeparableClosure K/K)) := by
  let Ω := SeparableClosure K
  let J₀ := finiteGaloisAbstractExtensionOfEmbedding K L i
  have hBase : intrinsicAbstractBase K = baseField Gal(Ω/K) :=
    closedFixingSubgroup_bot_eq_baseField K Ω
  exact
    { field := J₀.field
      below := le_baseField J₀.field
      normal := by
        change (J₀.field.toSubgroup.subgroupOf (baseField Gal(Ω/K)).toSubgroup).Normal
        rw [← hBase]
        exact J₀.normal
      finite := by
        change Finite ((baseField Gal(Ω/K)).toSubgroup ⧸
          J₀.field.toSubgroup.subgroupOf (baseField Gal(Ω/K)).toSubgroup)
        rw [← hBase]
        exact J₀.finite }

/-- The abstract norm subgroup of an embedded finite Galois extension is the
image of its actual determinant-norm range on the standard idèle classes. -/
theorem standardNumberFieldGaloisSubextensionOfEmbedding_normSubgroup
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (i : L →ₐ[K] SeparableClosure K) :
    (standardNumberFieldGaloisSubextensionOfEmbedding K L i).normSubgroup
        (ideleClassRepresentation K) =
      (NumberField.IdeleClassGroup.norm K L).range.toAddSubgroup.map
        (ideleClassEquivBaseFixed K).toAddMonoidHom := by
  let Ω := SeparableClosure K
  let J := standardNumberFieldGaloisSubextensionOfEmbedding K L i
  let F := abstractFixedField K Ω J.field
  let : FiniteDimensional K F := abstractFixedField_finiteDimensional K Ω J.field J.finite
  have hF : F = i.fieldRange := InfiniteGalois.fixedField_fixingSubgroup i.fieldRange
  let eL := i.equivFieldRange.trans (IntermediateField.equivOfEq hF.symm)
  have hSquare (x : K) :
      (eL.restrictScalars ℚ) (algebraMap K L x) =
        algebraMap K F ((AlgEquiv.refl : K ≃ₐ[ℚ] K) x) := by
    apply Subtype.ext
    exact i.commutes x
  have hRange : (NumberField.IdeleClassGroup.norm K F).range =
      (NumberField.IdeleClassGroup.norm K L).range := by
    have h := NumberField.IdeleClassGroup.norm_range_map_congr_of_compatible K L
      (AlgEquiv.refl : K ≃ₐ[ℚ] K) (eL.restrictScalars ℚ) hSquare
    have hId : (NumberField.IdeleClassGroup.congr (AlgEquiv.refl : K ≃ₐ[ℚ] K)).toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro c
      exact NumberField.IdeleClassGroup.congr_refl c
    rw [hId, Subgroup.map_id] at h
    exact h.symm
  rw [standardNumberFieldFiniteNormSubgroup K J, hRange]

/-- Any standard subgroup containing an actual finite Galois norm range is
the exact determinant-norm range of a finite abelian class field inside the
separable closure of the original base. -/
theorem exists_standardNumberFieldClassField_of_normRange_le
    (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (U : Subgroup (NumberField.IdeleClassGroup (𝓞 K) K))
    (hU : (NumberField.IdeleClassGroup.norm K L).range ≤ U) :
    ∃ J : FiniteAbelianSubextension (baseField Gal(SeparableClosure K/K)),
      let F := abstractFixedField K (SeparableClosure K) J.field
      letI : FiniteDimensional K F :=
        abstractFixedField_finiteDimensional K (SeparableClosure K) J.field J.finite
      (NumberField.IdeleClassGroup.norm K F).range = U := by
  let Ω := SeparableClosure K
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let J := standardNumberFieldGaloisSubextensionOfEmbedding K L i
  let e := ideleClassEquivBaseFixed K
  let U' := U.toAddSubgroup.map e.toAddMonoidHom
  have hOpen : IsNormOpen (ideleClassRepresentation K) (baseField Gal(Ω/K)) U' := by
    apply (normTopology_addSubgroup_isOpen_iff
      (ideleClassRepresentation K) (baseField Gal(Ω/K)) U').2
    refine ⟨J, ?_⟩
    rw [standardNumberFieldGaloisSubextensionOfEmbedding_normSubgroup K L i]
    exact AddSubgroup.map_mono hU
  obtain ⟨E, hE⟩ := FiniteAbelianSubextension.normSubgroupMap_surjective
    (numberFieldCyclotomicIdeleClassValuationData K)
    (ideleClassRepresentation_satisfiesClassFieldAxiom K)
    (FiniteAbstractField.base Gal(Ω/K)) ⟨U', hOpen⟩
  refine ⟨E, ?_⟩
  intro M
  let _ : FiniteDimensional K M :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) E.field E.finite
  have h := congrArg Subtype.val hE
  change E.toFiniteGaloisExtension.normSubgroup (ideleClassRepresentation K) = U' at h
  have hNorm := standardNumberFieldFiniteNormSubgroup K E.toFiniteGaloisExtension
  have hMap := hNorm.symm.trans h
  have h' := addSubgroup_eq_of_equiv_map_eq (ideleClassEquivBaseFixed K)
    (NumberField.IdeleClassGroup.norm K M).range.toAddSubgroup U.toAddSubgroup hMap
  exact congrArg AddSubgroup.toSubgroup h'

/-- Finite abelian existence and order reversal for the norm topology of
the same number-field formation. -/
noncomputable def numberFieldFiniteAbelianNormSubgroupOrderIso
    (H : FiniteAbstractField Gal(SeparableClosure K/K)) :
    FiniteAbelianSubextension H.field ≃o
      (FiniteAbelianSubextension.NormOpenAddSubgroup (ideleClassRepresentation K) H.field)ᵒᵈ :=
  FiniteAbelianSubextension.normSubgroupOrderIso (numberFieldCyclotomicIdeleClassValuationData K)
    (ideleClassRepresentation_satisfiesClassFieldAxiom K) H

end GlobalClassFieldTheory.Reciprocity
