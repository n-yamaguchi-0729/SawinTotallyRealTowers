/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Embeddings into a separable closure

This file provides the common realization of a separable extension inside the
chosen separable closure of its base field.
-/



@[expose] public section

noncomputable section

namespace AlgebraicNumberTheory

universe u v

/-- Conjugation by a field equivalence is continuous on automorphism
groups equipped with the Krull topology. -/
theorem continuous_algEquiv_autCongr
    {F E E' : Type*}
    [Field F] [Field E] [Field E']
    [Algebra F E] [Algebra F E']
    (e : E ≃ₐ[F] E') :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_continuousAt_one _
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hMfinite, hMs⟩ := hs
  let : FiniteDimensional F M := hMfinite
  let N : IntermediateField F E :=
    M.map e.symm.toAlgHom
  let : FiniteDimensional F N :=
    (M.equivMap e.symm.toAlgHom).toLinearEquiv.finiteDimensional
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨N, inferInstance, ?_⟩
  intro σ hσ
  apply hMs
  apply (IntermediateField.mem_fixingSubgroup_iff M
    (AlgEquiv.autCongr e σ)).2
  intro x hx
  have hxN : e.symm x ∈ N :=
    ⟨x, hx, rfl⟩
  have hfix :=
    (IntermediateField.mem_fixingSubgroup_iff N σ).1 hσ
      (e.symm x) hxN
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

/-- A chosen embedding of a separable extension into the separable closure of
its base field. -/
noncomputable def separableEmbeddingIntoSeparableClosure :
    L →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

/-- Two embeddings of a separable extension into the chosen separable
closure differ by an automorphism of that closure. -/
theorem exists_separableClosureEmbeddingComparisonAutomorphism
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    [Algebra.IsSeparable K L] (i j : L →ₐ[K] SeparableClosure K) :
    ∃ σ : Gal(SeparableClosure K/K), ∀ x : L, σ (i x) = j x := by
  let : Algebra L (SeparableClosure K) := i.toRingHom.toAlgebra
  let : IsScalarTower K L (SeparableClosure K) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  let : Algebra.IsSeparable L (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K L (SeparableClosure K)
  obtain ⟨f, hf⟩ := (IsSepClosed.surjective_domRestrict_of_isSeparable
    (K := K) (L := L) (M := SeparableClosure K) (E := SeparableClosure K)) j
  exact ⟨AlgEquiv.ofBijective f
    (Normal.toIsAlgebraic.algHom_bijective₂ f (AlgHom.id K (SeparableClosure K))).1,
    fun x => congrArg (fun g : L →ₐ[K] SeparableClosure K => g x) hf⟩

variable (K : Type*) [Field K] [NumberField K]

/-- A chosen `ℚ`-embedding of a number field into mathlib's fixed
separable closure of `ℚ`. -/
noncomputable def numberFieldSeparableClosureEmbedding :
    K →ₐ[ℚ] SeparableClosure ℚ :=
  IsSepClosed.lift

/-- The actual copy of `K` cut out by the chosen embedding into
`SeparableClosure ℚ`. -/
def numberFieldInRationalSeparableClosure :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  (numberFieldSeparableClosureEmbedding K).fieldRange

noncomputable instance
    numberFieldInRationalSeparableClosure_finiteDimensional :
    FiniteDimensional ℚ
      (numberFieldInRationalSeparableClosure K) :=
  ((numberFieldSeparableClosureEmbedding K).equivFieldRange.toLinearEquiv).finiteDimensional

noncomputable instance
    numberFieldInRationalSeparableClosure_numberField :
    NumberField (numberFieldInRationalSeparableClosure K) where
  to_charZero := inferInstance
  to_finiteDimensional := inferInstance

end AlgebraicNumberTheory
