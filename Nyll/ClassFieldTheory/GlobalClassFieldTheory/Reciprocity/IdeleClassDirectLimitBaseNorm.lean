/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormComparison
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassEmbeddingBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.FieldEquivNaturality
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixed
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteTowerNormCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedDescent
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableFixedFieldNorm

/-!
# Standard class norms to the base of the absolute limit

The abstract cosets are the actual embeddings of the upper field into its normal
closure. Their conjugate classes give the determinant norm for any finite extension.
-/

@[expose] public section

open scoped BigOperators NumberField
open ClassFormation CyclicCohomology KummerTheory LocalClassFieldTheory RamificationTheory

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

private theorem relativeClassComparison_embedding_of_le
    {F M : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K F] [FiniteDimensional K M] (h : F ≤ M)
    (d : RelativeIdeleGroup.ClassGroup K F) :
    NumberField.IdeleClassGroup.relativeClassComparison K M
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) d) =
      finiteIdeleClassEmbedding K h
        (NumberField.IdeleClassGroup.relativeClassComparison K F d) := by
  let : Algebra F M := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F M := FiniteDimensional.right K F M
  have hf : IntermediateField.inclusion h = IsScalarTower.toAlgHom K F M := by
    ext x
    rfl
  let e := relativeIdeleClassBaseChangeMulEquiv (K := K) (L := M)
  let a := relativeIdeleClassBaseChangeMulEquiv (K := K) (L := F) d
  have hd : e (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) d) =
      ideleClassExtension F M a :=
    (congrArg (fun f : F →ₐ[K] M => e (RelativeIdeleGroup.classEmbedding f d)) hf).trans
      (FiniteTowerNormCore.relativeIdeleClassBaseChange_classEmbedding_toAlgHom
        (K := K) (M := F) (L := M) d)
  exact hd

private theorem relativeClassEmbedding_directLimit_conjugation
    {F : IntermediateField K (SeparableClosure K)} [FiniteDimensional K F]
    (M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hFM : F ≤ M.toIntermediateField) (d : RelativeIdeleGroup.ClassGroup K F)
    (σ : Gal(SeparableClosure K/K)) :
    (ideleClassDirectLimitSMul K).smul σ (intermediateIdeleClassToDirectLimit K F
        (NumberField.IdeleClassGroup.relativeClassComparison K F d)) =
      finiteIdeleClassToDirectLimit K M (NumberField.IdeleClassGroup.relativeClassComparison K M
        (RelativeIdeleGroup.classEmbedding
          ((AlgEquiv.restrictNormalHom (↥M.toIntermediateField) σ).toAlgHom.comp
            (IntermediateField.inclusion hFM)) d)) := by
  let τ := AlgEquiv.restrictNormalHom (↥M.toIntermediateField) σ
  let j := IntermediateField.inclusion hFM
  let b := RelativeIdeleGroup.classEmbedding j d
  let R := NumberField.IdeleClassGroup.relativeClassComparison K M
  let T := NumberField.IdeleClassGroup.congr (τ.restrictScalars ℚ)
  have he := relativeClassComparison_embedding_of_le K hFM d
  have hConj := NumberField.IdeleClassGroup.relativeClassComparison_conjugation K M τ b
  have hComp := FiniteTowerNormCore.classEmbedding_smul_eq_classEmbedding_comp j τ d
  have h : T (finiteIdeleClassEmbedding K hFM
      (NumberField.IdeleClassGroup.relativeClassComparison K F d)) =
      R (RelativeIdeleGroup.classEmbedding (τ.toAlgHom.comp j) d) :=
    (congrArg T he.symm).trans (hConj.symm.trans (congrArg R hComp))
  rw [intermediateIdeleClassToDirectLimit_of_le K M hFM, finiteIdeleClassToDirectLimit_smul]
  exact congrArg (finiteIdeleClassToDirectLimit K M) h

private theorem relativeClassNorm_standardInclusion
    {F : IntermediateField K (SeparableClosure K)} [FiniteDimensional K F]
    (M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (d : RelativeIdeleGroup.ClassGroup K F) :
    NumberField.IdeleClassGroup.relativeClassComparison K M
        (RelativeIdeleGroup.classInclusion K M (RelativeIdeleGroup.classNorm K F d)) =
      NumberField.IdeleClassGroup.fieldInclusion K M
        (NumberField.IdeleClassGroup.norm K F
          (NumberField.IdeleClassGroup.relativeClassComparison K F d)) := by
  let n := RelativeIdeleGroup.classNorm K F d
  have hInc := NumberField.IdeleClassGroup.fieldInclusion_relativeClassComparison K M n
  have hNorm := NumberField.IdeleClassGroup.norm_relativeClassComparison K F d
  exact hInc.symm.trans (congrArg (NumberField.IdeleClassGroup.fieldInclusion K M) hNorm.symm)

private theorem relativeNorm_finiteEmbedding_sum
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (hFM : F ≤ M.toIntermediateField) (d : RelativeIdeleGroup.ClassGroup K F) :
    let Ω := SeparableClosure K
    let B := closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)
    let H := closedFixingSubgroup K Ω F
    let h := fixingSubgroupLeBase K Ω F
    let Q := B.toSubgroup ⧸ extensionSubgroup B H h
    ∀ (e : Q ≃ (F →ₐ[K] M)),
      (∀ σ : B.toSubgroup,
        e (QuotientGroup.mk σ) =
          (AlgEquiv.restrictNormalHom (↥M.toIntermediateField) σ.1).toAlgHom.comp
            (IntermediateField.inclusion hFM)) →
      (relativeNorm (ideleClassRepresentation K) B H h
          (ideleClassEquivFixed K F (Additive.ofMul
            (NumberField.IdeleClassGroup.relativeClassComparison K F d)))).1 =
        (MonoidHom.toAdditive ((finiteIdeleClassToDirectLimit K M).comp
          (NumberField.IdeleClassGroup.relativeClassComparison K M).toMonoidHom))
          (∑ j : F →ₐ[K] M, Additive.ofMul (RelativeIdeleGroup.classEmbedding j d)) := by
  intro Ω B H h Q e he
  let i := (finiteIdeleClassToDirectLimit K M).comp
    (NumberField.IdeleClassGroup.relativeClassComparison K M).toMonoidHom
  let a := ideleClassEquivFixed K F
    (Additive.ofMul (NumberField.IdeleClassGroup.relativeClassComparison K F d))
  have hAction (q : Q) :
      relativeCosetAction (ideleClassRepresentation K) B H h a q =
        Additive.ofMul (i (RelativeIdeleGroup.classEmbedding (e q) d)) := by
    refine Quotient.inductionOn' q ?_
    intro σ
    rw [relativeCosetAction_mk, he σ]
    exact congrArg Additive.ofMul (relativeClassEmbedding_directLimit_conjugation K M hFM d σ.1)
  exact relativeNorm_eq_mapped_sum (ideleClassRepresentation K) B H h a
    (MonoidHom.toAdditive i) e
    (fun j => Additive.ofMul (RelativeIdeleGroup.classEmbedding j d)) hAction

/-- The fixed-coefficient norm from any finite intermediate field is the standard
idele-class norm, included from the original base at the normal-closure level. -/
theorem ideleClassEquivFixed_relativeNormToBase_coe
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    let Ω := SeparableClosure K
    let B := closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)
    let H := closedFixingSubgroup K Ω F
    let M := finiteIdeleClassNormalClosure K F
    (relativeNorm (ideleClassRepresentation K) B H (fixingSubgroupLeBase K Ω F)
        (ideleClassEquivFixed K F (Additive.ofMul c))).1 =
      Additive.ofMul (finiteIdeleClassToDirectLimit K M
        (NumberField.IdeleClassGroup.fieldInclusion K M
          (NumberField.IdeleClassGroup.norm K F c))) := by
  intro Ω B H M
  obtain ⟨d, rfl⟩ := (NumberField.IdeleClassGroup.relativeClassComparison K F).surjective c
  let hFM : F ≤ M.toIntermediateField := IntermediateField.le_normalClosure F
  let : Algebra F M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  let : IsScalarTower K F M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F M := FiniteDimensional.right K F M
  let : CommGroup (RelativeIdeleGroup.ClassGroup K M) :=
    QuotientGroup.Quotient.commGroup (RelativeIdeleGroup.principalSubgroup K M)
  let Q := B.toSubgroup ⧸ extensionSubgroup B H (fixingSubgroupLeBase K Ω F)
  let e : Q ≃ (F →ₐ[K] M) :=
    (baseFixingCosetEquivAlgHom K Ω F).trans (normalClosure.algHomEquiv K F Ω).symm
  let i : RelativeIdeleGroup.ClassGroup K M →* ideleClassDirectLimit K :=
    (finiteIdeleClassToDirectLimit K M).comp
      (NumberField.IdeleClassGroup.relativeClassComparison K M).toMonoidHom
  have hRep (σ : B.toSubgroup) :
      e (QuotientGroup.mk σ) =
        (AlgEquiv.restrictNormalHom (↥M.toIntermediateField) σ.1).toAlgHom.comp
          (IntermediateField.inclusion hFM) := by
    apply AlgHom.ext
    intro x
    apply Subtype.ext
    change σ.1 (x : Ω) =
      (AlgEquiv.restrictNormalHom (↥M.toIntermediateField) σ.1
        (IntermediateField.inclusion hFM x) : Ω)
    exact (AlgEquiv.restrictNormal_commutes σ.1 M (IntermediateField.inclusion hFM x)).symm
  have hSum := relativeNorm_finiteEmbedding_sum K F M hFM d e hRep
  have hProd :
      (∑ j : F →ₐ[K] M, Additive.ofMul (RelativeIdeleGroup.classEmbedding j d)) =
        Additive.ofMul
          (RelativeIdeleGroup.classInclusion K M (RelativeIdeleGroup.classNorm K F d)) := by
    apply Additive.toMul.injective
    rw [toMul_sum]
    exact (RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_embeddings d).symm
  let toLimit (a : NumberField.IdeleClassGroup (𝓞 M) M) :=
    Additive.ofMul (finiteIdeleClassToDirectLimit K M a)
  have hLast := congrArg toLimit (relativeClassNorm_standardInclusion K M d)
  exact hSum.trans ((congrArg (MonoidHom.toAdditive i) hProd).trans hLast)

/-- The distinguished fixed part of the absolute limit consists of the original
standard idele classes of the base field. -/
noncomputable def ideleClassEquivBaseFixed :
    Additive (NumberField.IdeleClassGroup (𝓞 K) K) ≃+
      ambientFixedAddSubgroup (ideleClassRepresentation K)
        (baseField Gal(SeparableClosure K/K)) := by
  let B : IntermediateField K (SeparableClosure K) := ⊥
  let e : K ≃ₐ[K] B := (IntermediateField.botEquiv K (SeparableClosure K)).symm
  let : FiniteDimensional K B := e.toLinearEquiv.finiteDimensional
  let hB := closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)
  exact (MulEquiv.toAdditive (NumberField.IdeleClassGroup.congr (e.restrictScalars ℚ))).trans
    ((ideleClassEquivFixed K B).trans
      (AddEquiv.addSubgroupCongr
        (congrArg (ambientFixedAddSubgroup (ideleClassRepresentation K)) hB)))

/-- The base comparison places each original class at the actual scalar inclusion
at every finite Galois level. -/
theorem ideleClassEquivBaseFixed_coe
    (M : FiniteGaloisIntermediateField K (SeparableClosure K))
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    (ideleClassEquivBaseFixed K (Additive.ofMul c)).1 =
      Additive.ofMul (finiteIdeleClassToDirectLimit K M (NumberField.IdeleClassGroup.fieldInclusion
        K M c)) := by
  let B : IntermediateField K (SeparableClosure K) := ⊥
  let e : K ≃ₐ[K] B := (IntermediateField.botEquiv K (SeparableClosure K)).symm
  let : FiniteDimensional K B := e.toLinearEquiv.finiteDimensional
  let hBM : B ≤ M.toIntermediateField := bot_le
  let : Algebra B M := (IntermediateField.inclusion hBM).toRingHom.toAlgebra
  change Additive.ofMul (intermediateIdeleClassToDirectLimit K B
      (NumberField.IdeleClassGroup.congr (e.restrictScalars ℚ) c)) = _
  rw [intermediateIdeleClassToDirectLimit_of_le K M hBM]
  apply congrArg (fun b => Additive.ofMul (finiteIdeleClassToDirectLimit K M b))
  have hMap (x : K) : (AlgEquiv.refl : M ≃ₐ[ℚ] M) (algebraMap K M x) =
      algebraMap B M ((e.restrictScalars ℚ) x) := by
    apply Subtype.ext
    rfl
  have h := NumberField.IdeleClassGroup.congr_fieldInclusion (e.restrictScalars ℚ)
    (AlgEquiv.refl : M ≃ₐ[ℚ] M) hMap c
  rw [NumberField.IdeleClassGroup.congr_refl] at h
  exact h.symm

/-- The actual norm to the base fixed part is the norm of standard idele classes
from the fixed field of the original finite-index subgroup. -/
theorem abstractFixedFieldIdeleClassEquivFixed_normToBase
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    (c : NumberField.IdeleClassGroup (𝓞 (abstractFixedField K (SeparableClosure K) H.field))
      (abstractFixedField K (SeparableClosure K) H.field)) :
    normToBase (ideleClassRepresentation K) H.field
        (abstractFixedFieldIdeleClassEquivFixed K H.field (Additive.ofMul c)) =
      ideleClassEquivBaseFixed K (Additive.ofMul (NumberField.IdeleClassGroup.norm
        K (abstractFixedField K (SeparableClosure K) H.field) c)) := by
  let Ω := SeparableClosure K
  let F := abstractFixedField K Ω H.field
  let B := closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω)
  let J := closedFixingSubgroup K Ω F
  let x := ideleClassEquivFixed K F (Additive.ofMul c)
  let y := abstractFixedFieldIdeleClassEquivFixed K H.field (Additive.ofMul c)
  have hTransport := relativeNorm_coe_eq_of_closedSubgroup_eq (ideleClassRepresentation K)
    B (baseField Gal(Ω/K)) J H.field (fixingSubgroupLeBase K Ω F) (le_baseField H.field)
    (closedFixingSubgroup_bot_eq_baseField K Ω)
    (closedFixingSubgroup_abstractFixedField_eq K Ω H.field)
    x y rfl
  apply Subtype.ext
  rw [ideleClassEquivBaseFixed_coe K (finiteIdeleClassNormalClosure K F)]
  exact hTransport.symm.trans (ideleClassEquivFixed_relativeNormToBase_coe K F c)

end GlobalClassFieldTheory.Reciprocity
