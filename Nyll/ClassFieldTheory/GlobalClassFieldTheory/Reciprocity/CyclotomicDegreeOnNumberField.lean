/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitBaseNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldIntrinsicReciprocity.BaseComparison.IntrinsicBaseEquivalence
public import Nyll.GaloisCohomology.Topology.GaloisRestrictionScalars
public import Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-!
# The cyclotomic degree on the absolute Galois group of a number field

Restriction to the rational cyclotomic extension is normalized by the residue degree
of the actual embedded number field. The Krull comparison uses the chosen separable
closures and retains the restriction of each automorphism.
-/

@[expose] public section

open scoped NumberField
open AlgebraicNumberTheory ClassFormation KummerTheory LocalClassFieldTheory RamificationTheory

namespace GlobalClassFieldTheory.Reciprocity

universe u v

variable (K : Type u) [Field K] [NumberField K]

/-- The absolute Galois group of the original base is the fixing subgroup of its
chosen embedded copy in the rational separable closure. -/
noncomputable def numberFieldCyclotomicBaseSubgroupEquiv :
    Gal(SeparableClosure K/K) ≃ₜ* (numberFieldTowerBaseSubgroup K K).toSubgroup := by
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K K
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K K
  let : IsGalois K (SeparableClosure ℚ) := numberFieldTowerSeparableClosure_isGalois K K
  let eΩ : SeparableClosure K ≃ₐ[K] SeparableClosure ℚ := numberFieldTowerSeparableClosureEquiv K K
  let eAut := AlgEquiv.autCongr eΩ
  let e := eAut.trans (numberFieldTowerSeparableClosureEquivBaseSubgroup K K)
  have hcont : Continuous (fun σ : Gal(SeparableClosure K/K) =>
      (e σ : Gal(SeparableClosure ℚ/ℚ))) := by
    have h := (InfiniteGalois.restrictScalarsHom_continuous ℚ K (SeparableClosure ℚ)).comp
      (continuous_algEquiv_autCongr eΩ)
    exact h.congr (fun σ =>
      (numberFieldTowerSeparableClosureEquivBaseSubgroup_apply_coe K K (eAut σ)).symm)
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2 e.toMonoidHom
    (hcont.subtype_mk (fun σ => (e σ).property)) e.bijective

/-- The surjective cyclotomic degree on the original absolute Galois group. -/
noncomputable def numberFieldCyclotomicDegreeData : DegreeData Gal(SeparableClosure K/K) where
  degree :=
    (rationalCyclotomicDegreeData.normalizedDegree
      ((numberFieldTowerFiniteAbstractField K K).toFiniteResidueAbstractField
        rationalCyclotomicDegreeData)).comp
      (ContinuousMonoidHom.toContinuousMonoidHom (numberFieldCyclotomicBaseSubgroupEquiv K))
  degree_surjective :=
    (rationalCyclotomicDegreeData.normalizedDegree_surjective
      ((numberFieldTowerFiniteAbstractField K K).toFiniteResidueAbstractField
        rationalCyclotomicDegreeData)).comp (numberFieldCyclotomicBaseSubgroupEquiv K).surjective

/-- The base residue degree in the normalized Galois map is the intersection
degree used to normalize the standard class valuation. -/
theorem numberFieldCyclotomicBaseResidueDegree :
    ((numberFieldTowerFiniteAbstractField K K).residueDegree rationalCyclotomicDegreeData : ℕ) =
      cyclotomicZHatIntersectionDegree K := by
  let H := numberFieldTowerFiniteAbstractField K K
  have hLower : numberFieldTowerLowerEmbedding K K = numberFieldSeparableClosureEmbedding K := by
    apply AlgHom.ext
    intro x
    rfl
  have hFixed : abstractFixedField ℚ (SeparableClosure ℚ) H.field =
      numberFieldInRationalSeparableClosure K := by
    change IntermediateField.fixedField (numberFieldTowerBaseField K K).fixingSubgroup = _
    rw [InfiniteGalois.fixedField_fixingSubgroup]
    exact congrArg AlgHom.fieldRange hLower
  have hDegree := rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank H
  rw [hFixed] at hDegree
  exact hDegree

/-- Multiplying the normalized degree by the base residue degree restores the
actual rational restriction, with its original Frobenius orientation. -/
theorem numberFieldCyclotomicDegreeData_degree_mul
    (σ : Gal(SeparableClosure K/K)) :
    cyclotomicZHatIntersectionDegree K •
        ((numberFieldCyclotomicDegreeData K).degree σ).toAdd =
      (rationalCyclotomicDegreeData.degree
        (numberFieldCyclotomicBaseSubgroupEquiv K σ).1).toAdd := by
  rw [← numberFieldCyclotomicBaseResidueDegree K]
  exact rationalCyclotomicDegreeData.residueDegree_nsmul_normalizedDegree
    ((numberFieldTowerFiniteAbstractField K K).toFiniteResidueAbstractField
      rationalCyclotomicDegreeData) (numberFieldCyclotomicBaseSubgroupEquiv K σ)

/-- Under the actual closure equivalence, the rational automorphism acts
on the embedded element by the original automorphism. -/
theorem numberFieldCyclotomicBaseSubgroupEquiv_apply_embedding
    (σ : Gal(SeparableClosure K/K)) (x : SeparableClosure K) :
    let _ : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K K
    let e := numberFieldTowerSeparableClosureEquiv K K
    (numberFieldCyclotomicBaseSubgroupEquiv K σ).1 (e x) = e (σ x) := by
  intro embeddingAlgebra e
  change (numberFieldTowerSeparableClosureEquivBaseSubgroup K K (AlgEquiv.autCongr e σ)).1
    (e x) = e (σ x)
  have h := numberFieldTowerSeparableClosureEquivBaseSubgroup_apply_coe K K (AlgEquiv.autCongr e σ)
  exact (congrFun (congrArg DFunLike.coe h) (e x)).trans
    (congrArg (fun y => e (σ y)) (e.symm_apply_apply x))

/-- The cyclotomic intersection degree can be computed in any embedding
into the rational separable closure. -/
theorem cyclotomicZHatIntersectionDegree_eq_of_embedding
    (i : K →ₐ[ℚ] SeparableClosure ℚ) :
    cyclotomicZHatIntersectionDegree K =
      Module.finrank ℚ
      (i.fieldRange ⊓ rationalCyclotomicZHatField : IntermediateField ℚ (SeparableClosure ℚ)) := by
  let H : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ) :=
    ⟨closedFixingSubgroup ℚ (SeparableClosure ℚ) i.fieldRange,
      ambientEmbeddedAbsoluteQuotientFinite ℚ K i⟩
  let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
  have hF : F = i.fieldRange := InfiniteGalois.fixedField_fixingSubgroup i.fieldRange
  let e : K ≃ₐ[ℚ] F := i.equivFieldRange.trans (IntermediateField.equivOfEq hF.symm)
  let j := (numberFieldSeparableClosureEmbedding K).comp e.symm.toAlgHom
  have hImage : j.fieldRange = (numberFieldSeparableClosureEmbedding K).fieldRange := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨e x, congrArg (numberFieldSeparableClosureEmbedding K) (e.symm_apply_apply x)⟩
  have h := abstractFixedFieldCyclotomicZHatIntersection_finrank_eq_of_embedding H j
  rw [hImage] at h
  change cyclotomicZHatIntersectionDegree K =
    Module.finrank ℚ
      (i.fieldRange ⊓ rationalCyclotomicZHatField : IntermediateField ℚ (SeparableClosure ℚ))
  exact h.trans (congrArg (fun L : IntermediateField ℚ (SeparableClosure ℚ) =>
    Module.finrank ℚ
      (L ⊓ rationalCyclotomicZHatField : IntermediateField ℚ (SeparableClosure ℚ))) hF)

/-- The cyclotomic intersection degree is invariant under rational field equivalence. -/
theorem cyclotomicZHatIntersectionDegree_congr
    (L : Type v) [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L) :
    cyclotomicZHatIntersectionDegree K = cyclotomicZHatIntersectionDegree L := by
  let j := numberFieldSeparableClosureEmbedding L
  let i := j.comp e.toAlgHom
  have h : i.fieldRange = j.fieldRange := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e x, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨e.symm y, congrArg j (e.apply_symm_apply y)⟩
  exact (cyclotomicZHatIntersectionDegree_eq_of_embedding K i).trans
    (congrArg (fun F : IntermediateField ℚ (SeparableClosure ℚ) =>
      Module.finrank ℚ
        (F ⊓ rationalCyclotomicZHatField : IntermediateField ℚ (SeparableClosure ℚ))) h)

/-- Transporting the original class along a rational field equivalence
preserves its normalized cyclotomic value. -/
theorem standardCyclotomicIdeleClassValue_congr
    (L : Type v) [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L)
    (c : NumberField.IdeleClassGroup (𝓞 K) K) :
    standardCyclotomicIdeleClassValue L (Additive.ofMul (NumberField.IdeleClassGroup.congr e c)) =
      standardCyclotomicIdeleClassValue K (Additive.ofMul c) := by
  have hN := NumberField.IdeleClassGroup.norm_congr_of_compatible ℚ K
    (AlgEquiv.refl : ℚ ≃ₐ[ℚ] ℚ) e e.commutes c
  rw [NumberField.IdeleClassGroup.congr_refl] at hN
  apply zHatMulNat_injective (cyclotomicZHatIntersectionDegree_pos K)
  change cyclotomicZHatIntersectionDegree K • standardCyclotomicIdeleClassValue L
      (Additive.ofMul (NumberField.IdeleClassGroup.congr e c)) =
    cyclotomicZHatIntersectionDegree K • standardCyclotomicIdeleClassValue K (Additive.ofMul c)
  calc
    _ = cyclotomicZHatIntersectionDegree L • standardCyclotomicIdeleClassValue L
        (Additive.ofMul (NumberField.IdeleClassGroup.congr e c)) :=
      congrArg (fun n : ℕ => n • standardCyclotomicIdeleClassValue L
        (Additive.ofMul (NumberField.IdeleClassGroup.congr e c)))
          (cyclotomicZHatIntersectionDegree_congr K L e)
    _ = standardCyclotomicIdeleClassNormValue L
        (Additive.ofMul (NumberField.IdeleClassGroup.congr e c)) :=
      cyclotomicZHatIntersectionDegree_nsmul_standardIdeleClassValue L _
    _ = standardCyclotomicIdeleClassNormValue K (Additive.ofMul c) :=
      congrArg (fun a => rationalCyclotomicZHatIdeleClassValueContinuous
        (Additive.ofMul a)) hN.symm
    _ = _ := (cyclotomicZHatIntersectionDegree_nsmul_standardIdeleClassValue K _).symm

/-- For the actual finite fixed field, the relative residue degree is the
ratio of the two cyclotomic intersection degrees. -/
theorem numberFieldCyclotomicDegreeData_residueDegree_mul
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)] :
    let F := abstractFixedField K (SeparableClosure K) H.field
    cyclotomicZHatIntersectionDegree K * (H.residueDegree (numberFieldCyclotomicDegreeData K) : ℕ) =
      cyclotomicZHatIntersectionDegree F := by
  intro F
  let Ω := SeparableClosure K
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K K
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K K
  let eΩ : Ω ≃ₐ[K] SeparableClosure ℚ := numberFieldTowerSeparableClosureEquiv K K
  let e := numberFieldCyclotomicBaseSubgroupEquiv K
  let i : F →ₐ[ℚ] SeparableClosure ℚ :=
    (eΩ.restrictScalars ℚ).toAlgHom.comp (F.val.restrictScalars ℚ)
  let Hℚ : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ) :=
    { field := closedFixingSubgroup ℚ (SeparableClosure ℚ) i.fieldRange
      finite := ambientEmbeddedAbsoluteQuotientFinite ℚ F i }
  let B := numberFieldTowerBaseSubgroup K K
  have hHB : Hℚ.field.toSubgroup ≤ B.toSubgroup := by
    intro σ hσ
    change σ ∈ (numberFieldTowerBaseField K K).fixingSubgroup
    apply (IntermediateField.mem_fixingSubgroup_iff _ σ).2
    rintro _ ⟨a, rfl⟩
    have ha : i (algebraMap K F a) = numberFieldTowerLowerEmbedding K K a := eΩ.commutes a
    exact (IntermediateField.mem_fixingSubgroup_iff i.fieldRange σ).1 hσ
      (numberFieldTowerLowerEmbedding K K a) ⟨algebraMap K F a, ha⟩
  have hFix (σ : Gal(Ω/K)) :
      σ ∈ H.field.toSubgroup ↔ (e σ).1 ∈ Hℚ.field.toSubgroup := by
    have hH : F.fixingSubgroup = H.field.toSubgroup :=
      InfiniteGalois.fixingSubgroup_fixedField H.field
    change σ ∈ H.field.toSubgroup ↔ (e σ).1 ∈ i.fieldRange.fixingSubgroup
    rw [← hH, IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · rintro h _ ⟨x, rfl⟩
      change (e σ).1 (eΩ x.1) = eΩ x.1
      exact (numberFieldCyclotomicBaseSubgroupEquiv_apply_embedding K σ x.1).trans
        (congrArg eΩ (h x.1 x.2))
    · intro h x hx
      let xF : F := ⟨x, hx⟩
      have h' : (e σ).1 (eΩ x) = eΩ x := h (i xF) ⟨xF, rfl⟩
      exact eΩ.injective
        ((numberFieldCyclotomicBaseSubgroupEquiv_apply_embedding K σ x).symm.trans h')
  let D := numberFieldCyclotomicDegreeData K
  let f := cyclotomicZHatIntersectionDegree K
  let r := (H.residueDegree D : ℕ)
  have hImage :
      rationalCyclotomicDegreeData.fieldImageAdd Hℚ.field =
        (D.fieldImageAdd H.field).map (zHatMulNat f).toAddMonoidHom := by
    ext z
    rw [DegreeData.fieldImageAdd, Subgroup.mem_toAddSubgroup']
    constructor
    · rintro ⟨σ, hσ⟩
      let b : B.toSubgroup := ⟨σ.1, hHB σ.2⟩
      obtain ⟨τ, hτ⟩ := e.surjective b
      have hτH : τ ∈ H.field.toSubgroup := (hFix τ).2 (by rw [hτ]; exact σ.2)
      refine ⟨(D.degree τ).toAdd, ?_, ?_⟩
      · change D.degree τ ∈ D.fieldImage H.field
        exact ⟨⟨τ, hτH⟩, rfl⟩
      · change f • (D.degree τ).toAdd = z
        have heq := numberFieldCyclotomicDegreeData_degree_mul K τ
        change f • (D.degree τ).toAdd = (rationalCyclotomicDegreeData.degree (e τ).1).toAdd at heq
        rw [hτ] at heq
        exact heq.trans (congrArg Multiplicative.toAdd hσ)
    · rintro ⟨a, ha, haz⟩
      change Multiplicative.ofAdd a ∈ D.fieldImage H.field at ha
      obtain ⟨τ, hτ⟩ := ha
      refine ⟨⟨(e τ.1).1, (hFix τ.1).1 τ.2⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      calc
        _ = f • (D.degree τ.1).toAdd := (numberFieldCyclotomicDegreeData_degree_mul K τ.1).symm
        _ = f • a := congrArg (fun x : ZHat => f • x) (congrArg Multiplicative.toAdd hτ)
        _ = z := haz
  have hMulRange :
      ((zHatMulNat r).toAddMonoidHom.range.map (zHatMulNat f).toAddMonoidHom) =
        (zHatMulNat (f * r)).toAddMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, hx⟩
      refine ⟨x, ?_⟩
      change (f * r) • x = z
      rw [← smul_smul]
      exact hx
    · rintro ⟨x, rfl⟩
      refine ⟨r • x, ⟨x, rfl⟩, ?_⟩
      change f • (r • x) = (f * r) • x
      rw [smul_smul]
  have hDouble : (Hℚ.residueDegree rationalCyclotomicDegreeData : ℕ) = f * r := by
    let H₀ := H.toFiniteResidueAbstractField D
    let H₁ := Hℚ.toFiniteResidueAbstractField rationalCyclotomicDegreeData
    have hD : D.fieldImageAdd H.field = (zHatMulNat r).toAddMonoidHom.range :=
      D.fieldImageAdd_eq_mulNat_range H₀
    have h := hImage.trans ((congrArg (AddSubgroup.map (zHatMulNat f).toAddMonoidHom) hD).trans
      hMulRange)
    have hIndex := congrArg AddSubgroup.index h
    have hRange := zHatMulNat_range_index (f * r) (Nat.mul_pos
      (cyclotomicZHatIntersectionDegree_pos K) (H.residueDegree D).property)
    exact (rationalCyclotomicDegreeData.fieldImageAdd_index H₁).symm.trans
      (hIndex.trans hRange)
  let Fℚ := abstractFixedField ℚ (SeparableClosure ℚ) Hℚ.field
  have hF : Fℚ = i.fieldRange := InfiniteGalois.fixedField_fixingSubgroup i.fieldRange
  let eF : F ≃ₐ[ℚ] Fℚ := i.equivFieldRange.trans (IntermediateField.equivOfEq hF.symm)
  let j : Fℚ →ₐ[ℚ] SeparableClosure ℚ :=
    (numberFieldSeparableClosureEmbedding F).comp eF.symm.toAlgHom
  have hRange : j.fieldRange = (numberFieldSeparableClosureEmbedding F).fieldRange := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨eF.symm x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨eF x, congrArg (numberFieldSeparableClosureEmbedding F) (eF.symm_apply_apply x)⟩
  have hFDegree := abstractFixedFieldCyclotomicZHatIntersection_finrank_eq_of_embedding Hℚ j
  rw [hRange] at hFDegree
  exact hDouble.symm.trans
    ((rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank Hℚ).trans hFDegree.symm)

/-- The normalized class value on the distinguished fixed coefficients over the original base. -/
noncomputable def numberFieldCyclotomicClassValuation :
    ambientFixedAddSubgroup (ideleClassRepresentation K) (baseField Gal(SeparableClosure K/K)) →+
      ZHat :=
  (standardCyclotomicIdeleClassValue K).comp (ideleClassEquivBaseFixed K).symm.toAddMonoidHom

/-- The distinguished fixed-group valuation has full value group. -/
theorem numberFieldCyclotomicClassValuation_surjective :
    Function.Surjective (numberFieldCyclotomicClassValuation K) :=
  (standardCyclotomicIdeleClassValue_surjective K).comp (ideleClassEquivBaseFixed K).symm.surjective

/-- The actual abstract class norm scales its value by the upper and lower
cyclotomic intersection degrees. The upper fixed field need only be finite. -/
theorem numberFieldCyclotomicClassValuation_normToBase
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    (c : NumberField.IdeleClassGroup (𝓞 (abstractFixedField K (SeparableClosure K) H.field))
      (abstractFixedField K (SeparableClosure K) H.field)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    cyclotomicZHatIntersectionDegree K • numberFieldCyclotomicClassValuation K
        (normToBase (ideleClassRepresentation K) H.field
          (abstractFixedFieldIdeleClassEquivFixed K H.field (Additive.ofMul c))) =
      cyclotomicZHatIntersectionDegree F •
        standardCyclotomicIdeleClassValue F (Additive.ofMul c) := by
  intro F
  rw [abstractFixedFieldIdeleClassEquivFixed_normToBase]
  change cyclotomicZHatIntersectionDegree K • standardCyclotomicIdeleClassValue K
      ((ideleClassEquivBaseFixed K).symm
        (ideleClassEquivBaseFixed K (Additive.ofMul (NumberField.IdeleClassGroup.norm K F c)))) = _
  rw [AddEquiv.symm_apply_apply]
  exact standardCyclotomicIdeleClassValue_norm K F c

/-- The value of the abstract norm is the upper normalized class value
multiplied by the actual relative cyclotomic residue degree. -/
theorem numberFieldCyclotomicClassValuation_normToBase_eq_residueDegree
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    (c : NumberField.IdeleClassGroup (𝓞 (abstractFixedField K (SeparableClosure K) H.field))
      (abstractFixedField K (SeparableClosure K) H.field)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    numberFieldCyclotomicClassValuation K
        (normToBase (ideleClassRepresentation K) H.field
          (abstractFixedFieldIdeleClassEquivFixed K H.field (Additive.ofMul c))) =
      (H.residueDegree (numberFieldCyclotomicDegreeData K) : ℕ) •
        standardCyclotomicIdeleClassValue F (Additive.ofMul c) := by
  intro F
  apply zHatMulNat_injective (cyclotomicZHatIntersectionDegree_pos K)
  have h := numberFieldCyclotomicClassValuation_normToBase K H c
  change _ = cyclotomicZHatIntersectionDegree F • standardCyclotomicIdeleClassValue F
    (Additive.ofMul c) at h
  rw [← numberFieldCyclotomicDegreeData_residueDegree_mul K H, ← smul_smul] at h
  exact h

/-- The number-field coefficient representation has the actual cyclotomic
valuation data, including the norm range for every finite fixed field. -/
noncomputable def numberFieldCyclotomicIdeleClassValuationData :
    ValuationData (numberFieldCyclotomicDegreeData K) (ideleClassRepresentation K) where
  toAddMonoidHom := numberFieldCyclotomicClassValuation K
  integers_mem m := by
    rw [AddMonoidHom.range_eq_top_of_surjective _
      (numberFieldCyclotomicClassValuation_surjective K)]
    exact AddSubgroup.mem_top _
  canonical_value_quotient_bijective n hn := by
    rw [AddMonoidHom.range_eq_top_of_surjective _
      (numberFieldCyclotomicClassValuation_surjective K)]
    exact canonicalValueQuotientMap_top_bijective n hn
  norm_range H := by
    let F := abstractFixedField K (SeparableClosure K) H.field
    let : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H.field H.finite
    let e := abstractFixedFieldIdeleClassEquivFixed K H.field
    let v := standardCyclotomicIdeleClassValue F
    let r : ℕ := H.residueDegree (numberFieldCyclotomicDegreeData K)
    rw [AddMonoidHom.range_eq_top_of_surjective _
      (numberFieldCyclotomicClassValuation_surjective K)]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨c, rfl⟩ := e.surjective x
      exact ⟨v c, AddSubgroup.mem_top _,
        (numberFieldCyclotomicClassValuation_normToBase_eq_residueDegree K H c.toMul).symm⟩
    · rintro ⟨a, _, rfl⟩
      obtain ⟨c, hc⟩ := standardCyclotomicIdeleClassValue_surjective F a
      exact ⟨e c,
        (numberFieldCyclotomicClassValuation_normToBase_eq_residueDegree K H c.toMul).trans
        (congrArg (fun b : ZHat => r • b) hc)⟩

/-- The induced valuation of a finite fixed field equals its normalized
cyclotomic valuation on standard idele classes. -/
@[simp]
theorem numberFieldCyclotomicIdeleClassValuationData_valuationAt_apply
    (H : FiniteAbstractField Gal(SeparableClosure K/K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H.field)]
    (c : NumberField.IdeleClassGroup (𝓞 (abstractFixedField K (SeparableClosure K) H.field))
      (abstractFixedField K (SeparableClosure K) H.field)) :
    let F := abstractFixedField K (SeparableClosure K) H.field
    ((numberFieldCyclotomicIdeleClassValuationData K).valuationAt H
      (abstractFixedFieldIdeleClassEquivFixed K H.field (Additive.ofMul c)) : ZHat) =
      standardCyclotomicIdeleClassValue F (Additive.ofMul c) := by
  intro F
  let v := numberFieldCyclotomicIdeleClassValuationData K
  let a := abstractFixedFieldIdeleClassEquivFixed K H.field (Additive.ofMul c)
  apply zHatMulNat_injective (H.residueDegree (numberFieldCyclotomicDegreeData K)).property
  change (H.residueDegree (numberFieldCyclotomicDegreeData K) : ℕ) • v.dividedAt H a =
    (H.residueDegree (numberFieldCyclotomicDegreeData K) : ℕ) •
      standardCyclotomicIdeleClassValue F (Additive.ofMul c)
  exact (v.residueDegree_nsmul_dividedAt H a).trans
    (numberFieldCyclotomicClassValuation_normToBase_eq_residueDegree K H c)

/-- The original-field and rationally presented valuations have identical
values on the corresponding finite fixed-field classes. -/
theorem numberFieldCyclotomicIdeleClassValuationData_rational_valuationAt_apply
    (H : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ)) :
    let F := abstractFixedField ℚ (SeparableClosure ℚ) H.field
    letI : FiniteDimensional ℚ F :=
      abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) H.field H.finite
    ∀ c : _root_.IdeleClassGroup F,
    ((numberFieldCyclotomicIdeleClassValuationData ℚ).valuationAt H
      (abstractFixedFieldIdeleClassEquivFixed ℚ H.field
        (Additive.ofMul c)) : ZHat) =
      (rationalCyclotomicIdeleClassValuationData.valuationAt H
        (rationalAbstractFixedFieldIdeleClassEquivFixed H.field (Additive.ofMul c)) : ZHat) := by
  intro F c
  let fin : FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) H.field) :=
    abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ) H.field H.finite
  let _ : FiniteDimensional ℚ F := fin
  let _ : NumberField F := NumberField.of_module_finite ℚ F
  have h₁ := numberFieldCyclotomicIdeleClassValuationData_valuationAt_apply ℚ H c
  have h₃ := rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply H (Additive.ofMul c)
  exact h₁.trans h₃.symm

end GlobalClassFieldTheory.Reciprocity
