/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimit
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.FieldEquivNaturality
public import Mathlib.FieldTheory.Normal.Closure

/-!
# Finite intermediate fields in the standard idele-class limit

A finite intermediate field enters the same limit through its normal closure.
Functoriality of standard scalar inclusion makes this independent of the
chosen finite normal level. Its image is fixed by the actual fixing subgroup.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The canonical finite normal closure in the chosen separable closure. -/
def finiteIdeleClassNormalClosure
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    FiniteGaloisIntermediateField K (SeparableClosure K) :=
  { IntermediateField.normalClosure K F (SeparableClosure K) with
    finiteDimensional := normalClosure.is_finiteDimensional K F (SeparableClosure K)
    isGalois := IsGalois.normalClosure K F (SeparableClosure K) }

/-- The standard class group of any finite intermediate field maps into the
one direct limit through canonical inclusion into its normal closure. -/
def intermediateIdeleClassToDirectLimit
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    NumberField.IdeleClassGroup (𝓞 F) F →* ideleClassDirectLimit K :=
  (finiteIdeleClassToDirectLimit K (finiteIdeleClassNormalClosure K F)).comp
    (finiteIdeleClassEmbedding K (IntermediateField.le_normalClosure F))

/-- At a finite normal level, this is exactly the canonical limit map. -/
theorem intermediateIdeleClassToDirectLimit_finiteGalois
    (E : FiniteGaloisIntermediateField K (SeparableClosure K))
    (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    intermediateIdeleClassToDirectLimit K E c = finiteIdeleClassToDirectLimit K E c :=
  ideleClassDirectLimit_mk_apply K c (IntermediateField.le_normalClosure E.toIntermediateField)

/-- Inclusion of any two finite intermediate fields commutes with the same
absolute limit map. -/
theorem intermediateIdeleClassToDirectLimit_embedding
    {F E : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K F] [FiniteDimensional K E] (hFE : F ≤ E)
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    intermediateIdeleClassToDirectLimit K E (finiteIdeleClassEmbedding K hFE c) =
      intermediateIdeleClassToDirectLimit K F c := by
  let hFN : F ≤ (finiteIdeleClassNormalClosure K F).toIntermediateField :=
    IntermediateField.le_normalClosure F
  let hEN : E ≤ (finiteIdeleClassNormalClosure K E).toIntermediateField :=
    IntermediateField.le_normalClosure E
  let hN : finiteIdeleClassNormalClosure K F ≤ finiteIdeleClassNormalClosure K E :=
    IntermediateField.normalClosure_mono F E hFE
  change finiteIdeleClassToDirectLimit K (finiteIdeleClassNormalClosure K E)
      (finiteIdeleClassEmbedding K hEN (finiteIdeleClassEmbedding K hFE c)) = _
  rw [finiteIdeleClassEmbedding_comp]
  have hcomp := finiteIdeleClassEmbedding_comp K hFN hN c
  rw [← hcomp]
  exact ideleClassDirectLimit_mk_apply K (finiteIdeleClassEmbedding K hFN c) hN

/-- Any finite normal overfield computes the same intermediate-field map. -/
theorem intermediateIdeleClassToDirectLimit_of_le
    {F : IntermediateField K (SeparableClosure K)} [FiniteDimensional K F]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (hFE : F ≤ E.toIntermediateField)
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    intermediateIdeleClassToDirectLimit K F c =
      finiteIdeleClassToDirectLimit K E (finiteIdeleClassEmbedding K hFE c) := by
  rw [← intermediateIdeleClassToDirectLimit_finiteGalois]
  exact (intermediateIdeleClassToDirectLimit_embedding K hFE c).symm

/-- Finite scalar descent and injectivity of the transition maps give
injectivity for every finite intermediate field. -/
theorem intermediateIdeleClassToDirectLimit_injective
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    Function.Injective (intermediateIdeleClassToDirectLimit K F) :=
  (finiteIdeleClassToDirectLimit_injective K (finiteIdeleClassNormalClosure K F)).comp
    (finiteIdeleClassEmbedding_injective K (IntermediateField.le_normalClosure F))

/-- A class included from `F` is fixed by every absolute automorphism fixing
`F`, at any finite normal overfield. -/
theorem finiteIdeleClassEmbedding_fixed_of_mem_fixingSubgroup
    {F : IntermediateField K (SeparableClosure K)} [FiniteDimensional K F]
    (E : FiniteGaloisIntermediateField K (SeparableClosure K)) (hFE : F ≤ E.toIntermediateField)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (hσ : σ ∈ F.fixingSubgroup)
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    σ • finiteIdeleClassEmbedding K hFE c = finiteIdeleClassEmbedding K hFE c := by
  let : Algebra F E := (IntermediateField.inclusion hFE).toRingHom.toAlgebra
  change NumberField.IdeleClassGroup.congr (finiteIdeleClassAutomorphism K E σ)
      (NumberField.IdeleClassGroup.fieldInclusion F E c) = _
  have hcommute (x : F) :
      finiteIdeleClassAutomorphism K E σ (algebraMap F E x) =
        algebraMap F E ((AlgEquiv.refl : F ≃ₐ[ℚ] F) x) := by
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ E (IntermediateField.inclusion hFE x)).trans
      ((IntermediateField.mem_fixingSubgroup_iff F σ).1 hσ x.1 x.2)
  rw [NumberField.IdeleClassGroup.congr_fieldInclusion
    (AlgEquiv.refl : F ≃ₐ[ℚ] F) (finiteIdeleClassAutomorphism K E σ) hcommute c,
    NumberField.IdeleClassGroup.congr_refl]
  rfl

/-- The standard intermediate-field image is fixed in the absolute limit. -/
theorem intermediateIdeleClassToDirectLimit_fixed
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (hσ : σ ∈ F.fixingSubgroup)
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    (ideleClassDirectLimitSMul K).smul σ (intermediateIdeleClassToDirectLimit K F c) =
      intermediateIdeleClassToDirectLimit K F c := by
  let E := finiteIdeleClassNormalClosure K F
  let hFE : F ≤ E.toIntermediateField := IntermediateField.le_normalClosure F
  let z : NumberField.IdeleClassGroup (𝓞 E) E := finiteIdeleClassEmbedding K hFE c
  change (ideleClassDirectLimitSMul K).smul σ (finiteIdeleClassToDirectLimit K E z) =
    finiteIdeleClassToDirectLimit K E z
  exact (finiteIdeleClassToDirectLimit_smul K E σ z).trans
    (congrArg (finiteIdeleClassToDirectLimit K E)
      (finiteIdeleClassEmbedding_fixed_of_mem_fixingSubgroup K E hFE σ hσ c))

end GlobalClassFieldTheory.Reciprocity
