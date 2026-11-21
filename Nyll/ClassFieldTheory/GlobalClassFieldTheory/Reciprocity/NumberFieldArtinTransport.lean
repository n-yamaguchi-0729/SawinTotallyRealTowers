/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteReciprocityTransport
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicDegreeOnNumberField
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationNormQuotient
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitRationalComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldNormResidue
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData

/-!
# Transport of the number-field Artin calculation

Compatible closure maps identify corresponding finite fixed fields.
Standard idèle classes then transport with the same normalized valuation,
so the prime norm used by abstract reciprocity agrees under transport.
-/

@[expose] public section

open scoped NumberField
open ClassFormation CyclicCohomology KummerTheory LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u v

variable (K : Type u) [Field K] [NumberField K]

/-- Under a compatible comparison of lower absolute Galois groups, the
image of the finite fixed field is the corresponding rational fixed field. -/
theorem rationalIntermediateFieldImage_abstractFixedField
    (i : SeparableClosure K ≃ₐ[ℚ] SeparableClosure ℚ)
    (H S : ClosedSubgroup Gal(SeparableClosure K/K))
    (H' S' : ClosedSubgroup Gal(SeparableClosure ℚ/ℚ))
    (hSH : S.toSubgroup ≤ H.toSubgroup) (hS'H' : S'.toSubgroup ≤ H'.toSubgroup)
    (e : H.toSubgroup ≃ₜ* H'.toSubgroup)
    (he : ∀ s : H.toSubgroup, s.1 ∈ S.toSubgroup ↔ (e s).1 ∈ S'.toSubgroup)
    (hi : ∀ (s : H.toSubgroup) (x : SeparableClosure K), i (s.1 x) = (e s).1 (i x)) :
    rationalIntermediateFieldImage K i.toAlgHom (abstractFixedField K (SeparableClosure K) S) =
      abstractFixedField ℚ (SeparableClosure ℚ) S' := by
  let F := abstractFixedField K (SeparableClosure K) S
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    change i (x : SeparableClosure K) ∈ IntermediateField.fixedField S'.toSubgroup
    apply (IntermediateField.mem_fixedField_iff _ _).2
    intro τ hτ
    let t : H'.toSubgroup := ⟨τ, hS'H' hτ⟩
    obtain ⟨s, hs⟩ := e.surjective t
    have hsS : s.1 ∈ S.toSubgroup := (he s).2 (hs.symm ▸ hτ)
    change (t.1 : Gal(SeparableClosure ℚ/ℚ)) (i (x : SeparableClosure K)) = i (x :
      SeparableClosure K)
    rw [← hs, ← hi]
    exact congrArg i ((IntermediateField.mem_fixedField_iff _ _).1 x.2 s.1 hsS)
  · intro hz
    obtain ⟨x, rfl⟩ := i.surjective z
    have hx : x ∈ F := (IntermediateField.mem_fixedField_iff _ _).2 (by
      intro σ hσ
      let s : H.toSubgroup := ⟨σ, hSH hσ⟩
      apply i.injective
      change i (s.1 x) = i x
      rw [hi]
      exact (IntermediateField.mem_fixedField_iff _ _).1 hz (e s).1 ((he s).1 hσ))
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem rationalIntermediateClass_transport_field_eq
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E] (h : F = E)
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    intermediateIdeleClassToDirectLimit ℚ E
        (NumberField.IdeleClassGroup.congr (IntermediateField.equivOfEq h) c) =
      intermediateIdeleClassToDirectLimit ℚ F c := by
  subst E
  have hRefl : IntermediateField.equivOfEq (rfl : F = F) = (AlgEquiv.refl : F ≃ₐ[ℚ] F) := by
    apply AlgEquiv.ext
    intro x
    rfl
  rw [hRefl, NumberField.IdeleClassGroup.congr_refl]

private theorem rationalIntermediateClass_transport_congr
    {A : Type*} [Field A] [NumberField A]
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (e : A ≃ₐ[ℚ] F) (h : F = E) (c : NumberField.IdeleClassGroup (𝓞 A) A) :
    intermediateIdeleClassToDirectLimit ℚ E
        (NumberField.IdeleClassGroup.congr (e.trans (IntermediateField.equivOfEq h)) c) =
      intermediateIdeleClassToDirectLimit ℚ F (NumberField.IdeleClassGroup.congr e c) := by
  let f := intermediateIdeleClassToDirectLimit ℚ E
  have hc := NumberField.IdeleClassGroup.congr_trans e (IntermediateField.equivOfEq h) c
  exact (congrArg f hc.symm).trans
    (rationalIntermediateClass_transport_field_eq h (NumberField.IdeleClassGroup.congr e c))

private theorem ideleClassDirectLimitToRational_intermediate_eq
    (i : SeparableClosure K →ₐ[ℚ] SeparableClosure ℚ)
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (E : IntermediateField ℚ (SeparableClosure ℚ)) [FiniteDimensional ℚ E]
    (h : rationalIntermediateFieldImage K i F = E) (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    ideleClassDirectLimitToRational K i (intermediateIdeleClassToDirectLimit K F c) =
      intermediateIdeleClassToDirectLimit ℚ E (NumberField.IdeleClassGroup.congr
        ((rationalIntermediateFieldImageEquiv K i F).trans (IntermediateField.equivOfEq h)) c) := by
  have hf := ideleClassDirectLimitToRational_intermediate K i F c
  have hg := rationalIntermediateClass_transport_congr
      (rationalIntermediateFieldImageEquiv K i F) h c
  exact hf.trans hg.symm

private theorem rationalCyclotomicValuationAt_standard
    (S : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ))
    [FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) S.field)]
    (c : NumberField.IdeleClassGroup (𝓞 (abstractFixedField ℚ (SeparableClosure ℚ) S.field))
      (abstractFixedField ℚ (SeparableClosure ℚ) S.field)) :
    (rationalCyclotomicIdeleClassValuationData.valuationAt S
      (abstractFixedFieldIdeleClassEquivFixed ℚ S.field (Additive.ofMul c)) : ZHat) =
      standardCyclotomicIdeleClassValue (abstractFixedField ℚ (SeparableClosure ℚ) S.field)
        (Additive.ofMul c) := by
  exact rationalCyclotomicIdeleClassValuationData_valuationAt_fixed_apply S (Additive.ofMul c)

/-- The closure comparison preserves the normalized class valuation on
every pair of corresponding finite fixed fields. -/
theorem numberFieldCyclotomicValuationAt_transport
    (i : SeparableClosure K ≃ₐ[ℚ] SeparableClosure ℚ)
    (H : ClosedSubgroup Gal(SeparableClosure K/K)) (H' : ClosedSubgroup
        Gal(SeparableClosure ℚ/ℚ))
    (S : FiniteAbstractField Gal(SeparableClosure K/K))
    (S' : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ))
    (hSH : S.field.toSubgroup ≤ H.toSubgroup) (hS'H' : S'.field.toSubgroup ≤ H'.toSubgroup)
    (e : H.toSubgroup ≃ₜ* H'.toSubgroup)
    (he : ∀ s : H.toSubgroup, s.1 ∈ S.field.toSubgroup ↔ (e s).1 ∈ S'.field.toSubgroup)
    (hi : ∀ (s : H.toSubgroup) (x : SeparableClosure K), i (s.1 x) = (e s).1 (i x))
    (a : ambientFixedAddSubgroup (ideleClassRepresentation K) S.field)
    (a' : ambientFixedAddSubgroup (ideleClassRepresentation ℚ) S'.field)
    (ha : (MonoidHom.toAdditive (ideleClassDirectLimitToRational K i.toAlgHom)) a.1 = a'.1) :
    ((numberFieldCyclotomicIdeleClassValuationData K).valuationAt S a : ZHat) =
      (rationalCyclotomicIdeleClassValuationData.valuationAt S' a' : ZHat) := by
  let F := abstractFixedField K (SeparableClosure K) S.field
  let F' := abstractFixedField ℚ (SeparableClosure ℚ) S'.field
  let : FiniteDimensional K F := abstractFixedField_finiteDimensional K (SeparableClosure K)
    S.field S.finite
  let : FiniteDimensional ℚ F' := abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ)
    S'.field S'.finite
  let eR := rationalIntermediateFieldImageEquiv K i.toAlgHom F
  have hF := rationalIntermediateFieldImage_abstractFixedField K i H S.field H' S'.field hSH
    hS'H' e he hi
  let eF : F ≃ₐ[ℚ] F' := eR.trans (IntermediateField.equivOfEq hF)
  obtain ⟨c, hC⟩ := (abstractFixedFieldIdeleClassEquivFixed K S.field).surjective a
  let c' := NumberField.IdeleClassGroup.congr eF c.toMul
  have hC' : abstractFixedFieldIdeleClassEquivFixed ℚ S'.field (Additive.ofMul c') = a' := by
    apply Subtype.ext
    let f := (ideleClassDirectLimitToRational K i.toAlgHom).toAdditive
    have h₁ := abstractFixedFieldIdeleClassEquivFixed_coe K S.field c
    have h₂ := abstractFixedFieldIdeleClassEquivFixed_coe ℚ S'.field (Additive.ofMul c')
    have hStage := ideleClassDirectLimitToRational_intermediate_eq K i.toAlgHom F F' hF c.toMul
    have h₃ := congrArg Additive.ofMul hStage
    have h₄ := congrArg (fun a : ambientFixedAddSubgroup (ideleClassRepresentation K) S.field =>
      f a.val) hC
    exact h₂.trans (h₃.symm.trans ((congrArg f h₁).symm.trans (h₄.trans ha)))
  rw [← hC, ← hC']
  change ((numberFieldCyclotomicIdeleClassValuationData K).valuationAt S
      (abstractFixedFieldIdeleClassEquivFixed K S.field (Additive.ofMul c.toMul)) : ZHat) = _
  rw [numberFieldCyclotomicIdeleClassValuationData_valuationAt_apply,
    rationalCyclotomicValuationAt_standard]
  exact (standardCyclotomicIdeleClassValue_congr F F' eF c.toMul).symm

/-- The chosen original cyclotomic degree matches the normalized rational
degree under any compatible closure and lower-group comparison. -/
theorem numberFieldCyclotomicNormalizedDegree_transport
    (H' : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ))
    (i : SeparableClosure K ≃ₐ[ℚ] SeparableClosure ℚ)
    (e : (intrinsicFiniteAbstractBase K).field.toSubgroup ≃ₜ* H'.field.toSubgroup)
    (hi : ∀ (s : (intrinsicFiniteAbstractBase K).field.toSubgroup) (x : SeparableClosure K),
      i (s.1 x) = (e s).1 (i x))
    (s : (intrinsicFiniteAbstractBase K).field.toSubgroup) :
    (numberFieldCyclotomicDegreeData K).normalizedDegree
        ((intrinsicFiniteAbstractBase K).toFiniteResidueAbstractField
          (numberFieldCyclotomicDegreeData K)) s =
      rationalCyclotomicDegreeData.normalizedDegree (H'.toFiniteResidueAbstractField
        rationalCyclotomicDegreeData)
        (e s) := by
  let H := intrinsicFiniteAbstractBase K
  let D := numberFieldCyclotomicDegreeData K
  let D' := rationalCyclotomicDegreeData
  let R := H.toFiniteResidueAbstractField D
  let R' := H'.toFiniteResidueAbstractField D'
  let F := abstractFixedField K (SeparableClosure K) H.field
  let F' := abstractFixedField ℚ (SeparableClosure ℚ) H'.field
  let : FiniteDimensional ℚ F' := abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ)
    H'.field H'.finite
  have hF := rationalIntermediateFieldImage_abstractFixedField K i H.field H.field H'.field H'.field
    le_rfl le_rfl e (fun g => iff_of_true g.2 (e g).2) hi
  have hBot : F = (⊥ : IntermediateField K (SeparableClosure K)) :=
    InfiniteGalois.fixedField_fixingSubgroup (⊥ : IntermediateField K (SeparableClosure K))
  let eK : K ≃ₐ[ℚ] F :=
    ((IntermediateField.botEquiv K (SeparableClosure K)).symm.trans
      (IntermediateField.equivOfEq hBot.symm)).restrictScalars ℚ
  let eF : F ≃ₐ[ℚ] F' :=
    (rationalIntermediateFieldImageEquiv K i.toAlgHom F).trans (IntermediateField.equivOfEq hF)
  have hR' : (R'.residueDegree : ℕ) = cyclotomicZHatIntersectionDegree K :=
    (cyclotomicZHatIntersectionDegree_abstractFixedField_eq_residueDegree H').symm.trans
      (cyclotomicZHatIntersectionDegree_congr K F' (eK.trans eF)).symm
  have hR : (R.residueDegree : ℕ) = 1 := by
    change (H.residueDegree D : ℕ) = 1
    rw [show H = FiniteAbstractField.base Gal(SeparableClosure K/K) from
      intrinsicFiniteAbstractBase_eq_base K,
      FiniteAbstractField.base_residueDegree]
    rfl
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K K
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K K
  let i₀ := (numberFieldTowerSeparableClosureEquiv K K).restrictScalars ℚ
  let g₀ := (numberFieldCyclotomicBaseSubgroupEquiv K s.1).1
  let g₁ := (e s).1
  let t : Gal(SeparableClosure ℚ/ℚ) := i₀.symm.trans i
  have hConj : g₁ * t = t * g₀ := by
    apply AlgEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := i₀.surjective z
    have hLift : g₀ (i₀ x) = i₀ (s.1 x) :=
      numberFieldCyclotomicBaseSubgroupEquiv_apply_embedding K s.1 x
    change g₁ (i (i₀.symm (i₀ x))) = i (i₀.symm (g₀ (i₀ x)))
    simp only [hLift, i₀.symm_apply_apply]
    exact (hi s x).symm
  have hDegree : D'.degree g₀ = D'.degree g₁ := by
    have h := congrArg D'.degree hConj
    simp only [map_mul] at h
    exact mul_right_cancel ((mul_comm (D'.degree g₀) (D'.degree t)).trans h.symm)
  have hBase := D.residueDegree_nsmul_normalizedDegree R s
  rw [hR, one_smul] at hBase
  apply Multiplicative.toAdd.injective
  apply zHatMulNat_injective (cyclotomicZHatIntersectionDegree_pos K)
  change cyclotomicZHatIntersectionDegree K • (D.normalizedDegree R s).toAdd =
    cyclotomicZHatIntersectionDegree K • (D'.normalizedDegree R' (e s)).toAdd
  calc
    _ = cyclotomicZHatIntersectionDegree K • (D.degree s.1).toAdd :=
      congrArg (fun z : ZHat => cyclotomicZHatIntersectionDegree K • z) hBase
    _ = (D'.degree g₀).toAdd := numberFieldCyclotomicDegreeData_degree_mul K s.1
    _ = (D'.degree g₁).toAdd := congrArg Multiplicative.toAdd hDegree
    _ = (R'.residueDegree : ℕ) • (D'.normalizedDegree R' (e s)).toAdd :=
      (D'.residueDegree_nsmul_normalizedDegree R' (e s)).symm
    _ = _ := congrArg (fun n : ℕ => n • (D'.normalizedDegree R' (e s)).toAdd) hR'

private theorem degreeData_eq_of_degree_eq {G : Type*} [Group G] [TopologicalSpace G]
    (D D' : DegreeData G) (h : D.degree = D'.degree) : D = D' := by
  cases D
  cases D'
  cases h
  rfl

/-- The generic degree over the rational field is exactly its original
cyclotomic degree. -/
theorem numberFieldCyclotomicDegreeData_rat :
    numberFieldCyclotomicDegreeData ℚ = rationalCyclotomicDegreeData := by
  let G := Gal(SeparableClosure ℚ/ℚ)
  let H := intrinsicFiniteAbstractBase ℚ
  let H' := FiniteAbstractField.base G
  let D := numberFieldCyclotomicDegreeData ℚ
  let D' := rationalCyclotomicDegreeData
  have hB : H.field = H'.field := congrArg FiniteAbstractField.field
    (intrinsicFiniteAbstractBase_eq_base ℚ)
  let e : H.field.toSubgroup ≃ₜ* H'.field.toSubgroup :=
    { toFun := fun s => ⟨s.1, hB ▸ s.2⟩
      invFun := fun s => ⟨s.1, hB.symm ▸ s.2⟩
      left_inv := fun s => Subtype.ext rfl
      right_inv := fun s => Subtype.ext rfl
      map_mul' := fun s t => Subtype.ext rfl
      continuous_toFun := continuous_subtype_val.subtype_mk (fun s => hB ▸ s.2)
      continuous_invFun := continuous_subtype_val.subtype_mk (fun s => hB.symm ▸ s.2) }
  apply degreeData_eq_of_degree_eq
  apply ContinuousMonoidHom.ext
  intro σ
  let s : H.field.toSubgroup := ⟨σ, by
    rw [hB]
    exact Subgroup.mem_top _⟩
  have h := numberFieldCyclotomicNormalizedDegree_transport ℚ H'
    (AlgEquiv.refl : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) e (fun _ _ => rfl) s
  have hR : (H.residueDegree D : ℕ) = 1 := by
    rw [show H = H' from intrinsicFiniteAbstractBase_eq_base ℚ,
      FiniteAbstractField.base_residueDegree]
    rfl
  have hR' : (H'.residueDegree D' : ℕ) = 1 := by
    change ((FiniteAbstractField.base G).residueDegree D' : ℕ) = 1
    rw [FiniteAbstractField.base_residueDegree]
    rfl
  have h₁ := D.residueDegree_nsmul_normalizedDegree (H.toFiniteResidueAbstractField D) s
  have h₂ := D'.residueDegree_nsmul_normalizedDegree (H'.toFiniteResidueAbstractField D') (e s)
  change (H.residueDegree D : ℕ) • _ = _ at h₁
  change (H'.residueDegree D' : ℕ) • _ = _ at h₂
  rw [hR, one_smul] at h₁
  rw [hR', one_smul] at h₂
  apply Multiplicative.toAdd.injective
  exact h₁.symm.trans ((congrArg Multiplicative.toAdd h).trans h₂)

private theorem valuationAt_base_apply {G : Type*} [Group G] [TopologicalSpace G]
    {A : Rep ℤ G} {D : DegreeData G} (v : ValuationData D A)
    (a : ambientFixedAddSubgroup A (baseField G)) :
    (v.valuationAt (FiniteAbstractField.base G) a : ZHat) = v.toAddMonoidHom a := by
  let : Finite ((baseField G).toSubgroup ⧸
      extensionSubgroup (baseField G) (baseField G) (le_baseField (baseField G))) :=
    (FiniteAbstractField.base G).finite
  have h := v.residueDegree_nsmul_dividedAt (FiniteAbstractField.base G) a
  rw [FiniteAbstractField.base_residueDegree] at h
  change (1 : ℕ) • v.dividedAt (FiniteAbstractField.base G) a =
    v.toAddMonoidHom (relativeNorm A (baseField G) (baseField G) (le_baseField (baseField G))
      a) at h
  rw [one_smul, relativeNorm_self] at h
  exact h

private theorem numberFieldCyclotomicClassValuation_rat :
    numberFieldCyclotomicClassValuation ℚ = rationalCyclotomicZHatValuation := by
  apply AddMonoidHom.ext
  intro a
  let H := FiniteAbstractField.base Gal(SeparableClosure ℚ/ℚ)
  let v := numberFieldCyclotomicIdeleClassValuationData ℚ
  let v' := rationalCyclotomicIdeleClassValuationData
  let : Finite ((baseField Gal(SeparableClosure ℚ/ℚ)).toSubgroup ⧸
      extensionSubgroup (baseField Gal(SeparableClosure ℚ/ℚ)) H.field (le_baseField H.field))
        := H.finite
  obtain ⟨c, hc⟩ := (rationalAbstractFixedFieldIdeleClassEquivFixed H.field).surjective a
  have h := numberFieldCyclotomicIdeleClassValuationData_rational_valuationAt_apply H c.toMul
  change (v.valuationAt H (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) : ZHat) =
    (v'.valuationAt H (rationalAbstractFixedFieldIdeleClassEquivFixed H.field c) : ZHat) at h
  rw [hc] at h
  exact (valuationAt_base_apply v a).symm.trans (h.trans (valuationAt_base_apply v' a))

private theorem normResidueSymbol_eq_of_data_eq
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {A : Rep ℤ G} (D D' : DegreeData G) (hD : D = D')
    (v : ValuationData D A) (v' : ValuationData D' A) (hV : v.toAddMonoidHom = v'.toAddMonoidHom)
    (hcf : SatisfiesClassFieldAxiom A) (H : FiniteAbstractField G) (J :
      FiniteGaloisSubextension H.field) :
    D.normResidueSymbol A v hcf H J = D'.normResidueSymbol A v' hcf H J := by
  subst D'
  have h : v = v' := by
    cases v
    cases v'
    cases hV
    rfl
  rw [h]

/-- The generic finite norm-residue equivalence over the rationals retains
the same value at every rational fixed-field stage. -/
theorem numberFieldCyclotomicNormResidueSymbol_rat
    (H : FiniteAbstractField Gal(SeparableClosure ℚ/ℚ)) (J : FiniteGaloisSubextension H.field) :
    (numberFieldCyclotomicDegreeData ℚ).normResidueSymbol (ideleClassRepresentation ℚ)
        (numberFieldCyclotomicIdeleClassValuationData ℚ)
          (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ) H J =
      rationalCyclotomicDegreeData.normResidueSymbol (ideleClassRepresentation ℚ)
        rationalCyclotomicIdeleClassValuationData
            (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ) H J :=
  normResidueSymbol_eq_of_data_eq _ _ numberFieldCyclotomicDegreeData_rat _ _
    numberFieldCyclotomicClassValuation_rat
    (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ) H J

section Tower

open AlgebraicNumberTheory

variable (L : Type v) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The comparison of separable closures is chosen to extend the two
actual embeddings of the finite upper field. -/
def numberFieldTowerCompatibleClosureEquiv :
    let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
    SeparableClosure K ≃ₐ[K] SeparableClosure ℚ := by
  intro hAlg
  let : IsGalois K (SeparableClosure ℚ) := numberFieldTowerSeparableClosure_isGalois K L
  let e := numberFieldTowerSeparableClosureEquiv K L
  let i := e.toAlgHom.comp (separableEmbeddingIntoSeparableClosure K L)
  let j : L →ₐ[K] SeparableClosure ℚ :=
    { (numberFieldSeparableClosureEmbedding L).toRingHom with commutes' := fun _ => rfl }
  let jI := j.comp i.equivFieldRange.symm.toAlgHom
  let t := AlgEquiv.ofBijective (jI.liftNormal (SeparableClosure ℚ))
    (AlgHom.normal_bijective K (SeparableClosure ℚ) (SeparableClosure ℚ) _)
  exact e.trans t

omit [FiniteDimensional K L] in
/-- Both chosen embeddings of the top field are identified by the actual
closure comparison. -/
theorem numberFieldTowerCompatibleClosureEquiv_apply_top (x : L) :
    let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
    numberFieldTowerCompatibleClosureEquiv K L (separableEmbeddingIntoSeparableClosure K L x) =
      numberFieldSeparableClosureEmbedding L x := by
  intro hAlg
  let : IsGalois K (SeparableClosure ℚ) := numberFieldTowerSeparableClosure_isGalois K L
  let e := numberFieldTowerSeparableClosureEquiv K L
  let i := e.toAlgHom.comp (separableEmbeddingIntoSeparableClosure K L)
  let j : L →ₐ[K] SeparableClosure ℚ :=
    { (numberFieldSeparableClosureEmbedding L).toRingHom with commutes' := fun _ => rfl }
  let jI := j.comp i.equivFieldRange.symm.toAlgHom
  change jI.liftNormal (SeparableClosure ℚ) (algebraMap i.fieldRange (SeparableClosure ℚ)
    (i.equivFieldRange x)) =
    j x
  rw [jI.liftNormal_commutes]
  change j (i.equivFieldRange.symm (i.equivFieldRange x)) = j x
  rw [i.equivFieldRange.symm_apply_apply]

/-- The closure comparison identifies the original lower group with the
lower subgroup of the rational presentation. -/
def numberFieldTowerCompatibleBaseSubgroupEquiv :
    (intrinsicFiniteAbstractBase K).field.toSubgroup ≃ₜ* (numberFieldTowerBaseSubgroup K
      L).toSubgroup := by
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
  let : IsGalois K (SeparableClosure ℚ) := numberFieldTowerSeparableClosure_isGalois K L
  let i := numberFieldTowerCompatibleClosureEquiv K L
  let eK : (intrinsicFiniteAbstractBase K).field.toSubgroup ≃* Gal(SeparableClosure K/K) :=
    { toFun := Subtype.val
      invFun := fun σ => ⟨σ, by
        change σ ∈ (intrinsicAbstractBase K).toSubgroup
        rw [intrinsicAbstractBase, closedFixingSubgroup_bot_eq_baseField, baseField_toSubgroup]
        exact Subgroup.mem_top _⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let e := (eK.trans (AlgEquiv.autCongr i)).trans
      (numberFieldTowerSeparableClosureEquivBaseSubgroup K L)
  have h : Continuous (fun σ : (intrinsicFiniteAbstractBase K).field.toSubgroup =>
      (e σ : Gal(SeparableClosure ℚ/ℚ))) := by
    have hCont := ((InfiniteGalois.restrictScalarsHom_continuous ℚ K (SeparableClosure ℚ)).comp
      (continuous_algEquiv_autCongr i)).comp (continuous_subtype_val :
        Continuous (Subtype.val : (intrinsicFiniteAbstractBase K).field.toSubgroup →
          Gal(SeparableClosure K/K)))
    exact hCont.congr (fun σ =>
      (numberFieldTowerSeparableClosureEquivBaseSubgroup_apply_coe K L (AlgEquiv.autCongr i
        σ.1)).symm)
  let : CompactSpace (intrinsicFiniteAbstractBase K).field.toSubgroup :=
    isCompact_iff_compactSpace.mp (intrinsicFiniteAbstractBase K).field.isClosed'.isCompact
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2 e.toMonoidHom
    (h.subtype_mk (fun σ => (e σ).property)) e.bijective

omit [FiniteDimensional K L] in
/-- The continuous lower-group comparison acts by the conjugated
automorphism pointwise on the closure. -/
theorem numberFieldTowerCompatibleBaseSubgroupEquiv_apply
    (s : (intrinsicFiniteAbstractBase K).field.toSubgroup) (x : SeparableClosure K) :
    let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
    let i := numberFieldTowerCompatibleClosureEquiv K L
    i (s.1 x) = (numberFieldTowerCompatibleBaseSubgroupEquiv K L s).1 (i x) := by
  intro hAlg i
  change i (s.1 x) = (numberFieldTowerSeparableClosureEquivBaseSubgroup K L
    (AlgEquiv.autCongr i s.1)).1 (i x)
  have h := numberFieldTowerSeparableClosureEquivBaseSubgroup_apply_coe K L
    (AlgEquiv.autCongr i s.1)
  exact (congrArg (fun z => i (s.1 z)) (i.symm_apply_apply x)).symm.trans
    (congrArg (fun σ : Gal(SeparableClosure ℚ/ℚ) => σ (i x)) h).symm

/-- The lower-group comparison takes the subgroup fixing the original
top field onto the subgroup fixing its embedded rational model. -/
theorem numberFieldTowerCompatibleBaseSubgroupEquiv_mem_top
    (s : (intrinsicFiniteAbstractBase K).field.toSubgroup) :
    s.1 ∈ (finiteGaloisAbstractExtension K L).field.toSubgroup ↔
      (numberFieldTowerCompatibleBaseSubgroupEquiv K L s).1 ∈ (numberFieldTowerTopSubgroup
        L).toSubgroup := by
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let i := numberFieldTowerCompatibleClosureEquiv K L
  let τ := (numberFieldTowerCompatibleBaseSubgroupEquiv K L s).1
  let jK := separableEmbeddingIntoSeparableClosure K L
  let jℚ := numberFieldSeparableClosureEmbedding L
  have h (x : L) : i (jK x) = jℚ x := numberFieldTowerCompatibleClosureEquiv_apply_top K L x
  change s.1 ∈ jK.fieldRange.fixingSubgroup ↔ τ ∈ jℚ.fieldRange.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · rintro hs _ ⟨x, rfl⟩
    change τ (jℚ x) = jℚ x
    rw [← h x, ← numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L s (jK x)]
    exact congrArg i (hs (jK x) ⟨x, rfl⟩)
  · rintro hτ _ ⟨x, rfl⟩
    apply i.injective
    change i (s.1 (jK x)) = i (jK x)
    exact (numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L s (jK x)).trans
      ((congrArg τ (h x)).trans ((hτ (jℚ x) ⟨x, rfl⟩).trans (h x).symm))

private def numberFieldTowerCoefficientTransport :
    (ideleClassRepresentation K).V →+ (ideleClassRepresentation ℚ).V := by
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
  let f := ideleClassDirectLimitToRational K
    ((numberFieldTowerCompatibleClosureEquiv K L).restrictScalars ℚ).toAlgHom
  exact f.toAdditive

omit [FiniteDimensional K L] in
private theorem numberFieldTowerCoefficientTransport_equivariant
    (s : (intrinsicFiniteAbstractBase K).field.toSubgroup) (a : (ideleClassRepresentation K).V) :
    numberFieldTowerCoefficientTransport K L ((ideleClassRepresentation K).ρ s.1 a) =
      (ideleClassRepresentation ℚ).ρ (numberFieldTowerCompatibleBaseSubgroupEquiv K L s).1
        (numberFieldTowerCoefficientTransport K L a) := by
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
  let i := (numberFieldTowerCompatibleClosureEquiv K L).restrictScalars ℚ
  exact congrArg Additive.ofMul (ideleClassDirectLimitToRational_smul K i.toAlgHom s.1
    (numberFieldTowerCompatibleBaseSubgroupEquiv K L s).1
    (numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L s) a.toMul)

/-- After transporting actual norm classes, the original and rational
finite reciprocity homomorphisms assign the same class to each automorphism. -/
private theorem numberFieldTower_finiteReciprocityHom_transport
    (q : (intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
      extensionSubgroup (intrinsicFiniteAbstractBase K).field (finiteGaloisAbstractExtension
        K L).field
        (finiteGaloisAbstractExtension K L).below) :
    let H := intrinsicFiniteAbstractBase K
    let H' := numberFieldTowerFiniteAbstractField K L
    let J := finiteGaloisAbstractExtension K L
    let J' := numberFieldTowerFiniteGaloisSubextension K L
    let e := numberFieldTowerCompatibleBaseSubgroupEquiv K L
    let he := numberFieldTowerCompatibleBaseSubgroupEquiv_mem_top K L
    let f := numberFieldTowerCoefficientTransport K L
    let hf := numberFieldTowerCoefficientTransport_equivariant K L
    let D := numberFieldCyclotomicDegreeData K
    let v := numberFieldCyclotomicIdeleClassValuationData K
    let D' := rationalCyclotomicDegreeData
    let v' := rationalCyclotomicIdeleClassValuationData
    let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology
      (ideleClassRepresentation_satisfiesClassFieldAxiom K)
    let hAxiom' := v'.classFieldAxiom_implies_unramifiedUnitCohomology
      (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
    letI : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) := J.finite
    letI : Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field J'.field
        J'.below) := J'.finite
    finiteNormQuotientTransport (ideleClassRepresentation K) (ideleClassRepresentation ℚ)
      H H' J J' e he f hf
        (D.finiteReciprocityHom (ideleClassRepresentation K) v hAxiom H J.field J.below
          (Additive.ofMul q)) =
      D'.finiteReciprocityHom (ideleClassRepresentation ℚ) v' hAxiom' H' J'.field
        J'.below (Additive.ofMul
        (relativeCosetEquivOfMulEquiv J.below J'.below e.toMulEquiv he q)) := by
  dsimp only
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
  let i := (numberFieldTowerCompatibleClosureEquiv K L).restrictScalars ℚ
  apply finiteReciprocityHom_transport
  · exact numberFieldCyclotomicNormalizedDegree_transport K
      (numberFieldTowerFiniteAbstractField K L) i (numberFieldTowerCompatibleBaseSubgroupEquiv K L)
      (numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L)
  · intro S S' hSH hS'H' hS a a' ha
    exact numberFieldCyclotomicValuationAt_transport K i _ _ S S' hSH hS'H'
      (numberFieldTowerCompatibleBaseSubgroupEquiv K L) hS
      (numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L) a a' ha

omit [FiniteDimensional K L] in
private theorem numberFieldTowerCoefficientTransport_base_class (c : _root_.IdeleClassGroup K) :
    finiteReciprocityBaseCoefficientsMap (ideleClassRepresentation K)
      (ideleClassRepresentation ℚ)
        (intrinsicFiniteAbstractBase K) (numberFieldTowerFiniteAbstractField K L)
        (numberFieldTowerCompatibleBaseSubgroupEquiv K L)
        (numberFieldTowerCoefficientTransport K L)
          (numberFieldTowerCoefficientTransport_equivariant K L)
        (standardNumberFieldClassEquivIntrinsicFixed K
          (Additive.ofMul c)) =
      numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c) := by
  let H := intrinsicFiniteAbstractBase K
  let H' := numberFieldTowerFiniteAbstractField K L
  let F := abstractFixedField K (SeparableClosure K) H.field
  let F' := abstractFixedField ℚ (SeparableClosure ℚ) H'.field
  let eK := FunctionField.finiteGaloisBaseFixedFieldEquiv K
  let eOld := numberFieldTowerAbstractBaseFieldEquiv K L
  let : FiniteDimensional K F := eK.toLinearEquiv.finiteDimensional
  let : FiniteDimensional ℚ F' := abstractFixedField_finiteDimensional ℚ (SeparableClosure ℚ)
    H'.field H'.finite
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let : IsScalarTower ℚ K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseScalarTower K L
  let iK := numberFieldTowerCompatibleClosureEquiv K L
  let i := iK.restrictScalars ℚ
  let ψ := numberFieldTowerCompatibleBaseSubgroupEquiv K L
  let eR := rationalIntermediateFieldImageEquiv K i.toAlgHom F
  have hF := rationalIntermediateFieldImage_abstractFixedField K i H.field H.field H'.field H'.field
    le_rfl le_rfl ψ (fun s => iff_of_true s.2 (ψ s).2)
      (numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L)
  let eF := IntermediateField.equivOfEq hF
  have hComp : ((eK.restrictScalars ℚ).trans eR).trans eF = eOld := by
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change iK (eK x : SeparableClosure K) = numberFieldTowerLowerEmbedding K L x
    have hx : eK x = algebraMap K F x := eK.commutes x
    rw [hx]
    exact iK.commutes x
  let dF := NumberField.IdeleClassGroup.congr (eK.restrictScalars ℚ) c
  apply Subtype.ext
  change Additive.ofMul (ideleClassDirectLimitToRational K i.toAlgHom
      (intermediateIdeleClassToDirectLimit K F dF)) =
    Additive.ofMul (intermediateIdeleClassToDirectLimit ℚ F'
      (NumberField.IdeleClassGroup.congr eOld c))
  have ht := ideleClassDirectLimitToRational_intermediate_eq K i.toAlgHom F F' hF dF
  have h₂ := NumberField.IdeleClassGroup.congr_trans (eK.restrictScalars ℚ) (eR.trans eF) c
  have hAssoc : (eK.restrictScalars ℚ).trans (eR.trans eF) = eOld := hComp
  have h₃ := congrArg (fun e : K ≃ₐ[ℚ] F' => NumberField.IdeleClassGroup.congr e c) hAssoc
  let f := intermediateIdeleClassToDirectLimit ℚ F'
  exact congrArg Additive.ofMul (ht.trans (congrArg f (h₂.trans h₃)))

private theorem numberFieldTowerQuotientTransport_galois_apply
    (q : (intrinsicFiniteAbstractBase K).field.toSubgroup ⧸
      extensionSubgroup (intrinsicFiniteAbstractBase K).field (finiteGaloisAbstractExtension
        K L).field
        (finiteGaloisAbstractExtension K L).below) :
    numberFieldTowerExtensionQuotientEquivGaloisGroup K L
        (relativeCosetEquivOfMulEquiv (finiteGaloisAbstractExtension K L).below
          (numberFieldTowerFiniteGaloisSubextension K L).below
          (numberFieldTowerCompatibleBaseSubgroupEquiv K L).toMulEquiv
          (numberFieldTowerCompatibleBaseSubgroupEquiv_mem_top K L) q) =
      finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
        (separableEmbeddingIntoSeparableClosure K L) q := by
  refine Quotient.inductionOn' q ?_
  intro s
  let : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let i := numberFieldTowerCompatibleClosureEquiv K L
  let ψ := numberFieldTowerCompatibleBaseSubgroupEquiv K L
  let jK := separableEmbeddingIntoSeparableClosure K L
  let jℚ := numberFieldSeparableClosureEmbedding L
  apply AlgEquiv.ext
  intro x
  apply jℚ.injective
  change jℚ (numberFieldTowerExtensionQuotientEquivGaloisGroup K L (QuotientGroup.mk (ψ s)) x) =
    jℚ (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L jK (QuotientGroup.mk s) x)
  have hOld := ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply ℚ K L jℚ
    (numberFieldTowerSeparableClosureEquiv K L) (ψ s) x
  have hNew := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K L jK s x
  calc
    _ = (ψ s).1 (jℚ x) := hOld
    _ = i (s.1 (jK x)) := by
      rw [← numberFieldTowerCompatibleClosureEquiv_apply_top K L x,
        ← numberFieldTowerCompatibleBaseSubgroupEquiv_apply K L s (jK x)]
    _ = i (jK (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L jK
      (QuotientGroup.mk s) x)) :=
      congrArg i hNew.symm
    _ = _ := numberFieldTowerCompatibleClosureEquiv_apply_top K L _

/-- The standard Artin map agrees pointwise with the rational presentation
of the same finite norm-residue symbol and actual Galois quotient. -/
theorem standardNumberFieldArtin_transport
    (c : _root_.IdeleClassGroup K) :
    let H' := numberFieldTowerFiniteAbstractField K L
    let J' := numberFieldTowerFiniteGaloisSubextension K L
    letI : Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field J'.field
        J'.below) := J'.finite
    standardNumberFieldArtin K L c =
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L).abelianizationCongr
        ((rationalCyclotomicDegreeData.normResidueSymbol (ideleClassRepresentation ℚ)
          rationalCyclotomicIdeleClassValuationData
            (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ) H' J'
          (finiteNormClass (ideleClassRepresentation ℚ) H'.field J'.field J'.below
            (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c)))).toMul) := by
  intro H' J'
  let : Finite (H'.field.toSubgroup ⧸ extensionSubgroup H'.field J'.field J'.below) := J'.finite
  let A := ideleClassRepresentation K
  let H := intrinsicFiniteAbstractBase K
  let J := finiteGaloisAbstractExtension K L
  let D := numberFieldCyclotomicDegreeData K
  let v := numberFieldCyclotomicIdeleClassValuationData K
  let hcf := ideleClassRepresentation_satisfiesClassFieldAxiom K
  let hAxiom := v.classFieldAxiom_implies_unramifiedUnitCohomology hcf
  let v' := rationalCyclotomicIdeleClassValuationData
  let hcf' := (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
  let hAxiom' := v'.classFieldAxiom_implies_unramifiedUnitCohomology hcf'
  let : Finite (H.field.toSubgroup ⧸ extensionSubgroup H.field J.field J.below) := J.finite
  let e := numberFieldTowerCompatibleBaseSubgroupEquiv K L
  let he := numberFieldTowerCompatibleBaseSubgroupEquiv_mem_top K L
  let f := numberFieldTowerCoefficientTransport K L
  let hf := numberFieldTowerCoefficientTransport_equivariant K L
  let x := finiteNormClass A H.field J.field J.below (standardNumberFieldClassEquivIntrinsicFixed K
    (Additive.ofMul c))
  let x' := finiteNormClass (ideleClassRepresentation ℚ) H'.field J'.field J'.below
    (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c))
  obtain ⟨q, hq⟩ := v.abstractReciprocity_finiteReciprocityHom_surjective hcf hAxiom H J x
  let q' := relativeCosetEquivOfMulEquiv J.below J'.below e.toMulEquiv he q.toMul
  have hq' : rationalCyclotomicDegreeData.finiteReciprocityHom (ideleClassRepresentation ℚ)
      v' hAxiom' H' J'.field J'.below (Additive.ofMul q') = x' := by
    have h := numberFieldTower_finiteReciprocityHom_transport K L q.toMul
    change finiteNormQuotientTransport A (ideleClassRepresentation ℚ) H H' J J' e he f hf
      (D.finiteReciprocityHom A v hAxiom H J.field J.below q) = _ at h
    rw [hq] at h
    rw [← h]
    change finiteNormQuotientTransport A (ideleClassRepresentation ℚ) H H' J J' e he f hf
      (finiteNormClass A H.field J.field J.below (standardNumberFieldClassEquivIntrinsicFixed K
        (Additive.ofMul c))) = x'
    let b := standardNumberFieldClassEquivIntrinsicFixed K
      (Additive.ofMul c)
    have hb := finiteNormQuotientTransport_finiteNormClass A (ideleClassRepresentation ℚ)
      H H' J J' e he f hf b
    exact hb.trans (congrArg (finiteNormClass (ideleClassRepresentation ℚ) H'.field
      J'.field J'.below)
      (numberFieldTowerCoefficientTransport_base_class K L c))
  rw [standardNumberFieldArtin_finiteNormClass]
  change (J.extensionQuotientMulEquiv.trans
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
        (separableEmbeddingIntoSeparableClosure K L))).abelianizationCongr
        ((D.normResidueSymbol A v hcf H J x).toMul) =
    (numberFieldTowerExtensionQuotientEquivGaloisGroup K L).abelianizationCongr
      ((rationalCyclotomicDegreeData.normResidueSymbol (ideleClassRepresentation ℚ) v'
        hcf' H' J' x').toMul)
  have hOriginal := (congrArg (D.normResidueSymbol A v hcf H J) hq).symm.trans
    (D.normResidueSymbol_finiteReciprocityHom A v hcf H J q.toMul)
  have hRational := (congrArg (rationalCyclotomicDegreeData.normResidueSymbol
    (ideleClassRepresentation ℚ) v' hcf' H' J') hq').symm.trans
    (rationalCyclotomicDegreeData.normResidueSymbol_finiteReciprocityHom
      (ideleClassRepresentation ℚ) v' hcf' H' J' q')
  rw [hOriginal, hRational]
  let eBase : J.extensionQuotient ≃* Gal(L/K) :=
    finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
      (separableEmbeddingIntoSeparableClosure K L)
  let eOriginal := J.extensionQuotientMulEquiv.trans eBase
  let eRational := numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  have h := numberFieldTowerQuotientTransport_galois_apply K L q.toMul
  exact (Group.abelianizationCongr_of eOriginal q.toMul).trans
    ((congrArg Group.Abelianization.of h.symm).trans
      (Group.abelianizationCongr_of eRational q').symm)

end Tower

end GlobalClassFieldTheory.Reciprocity
