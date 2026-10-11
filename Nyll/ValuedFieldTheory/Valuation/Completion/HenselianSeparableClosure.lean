/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.NormedGaloisIsometry
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Separable algebraic closure of a Henselian field in its completion

In a finite normal extension, the Henselian valuation is invariant under
ground-field automorphisms. An element approximable by ground-field elements
must therefore be fixed by every automorphism. Applying this to the splitting
field of a separable element in an algebraic closure of the completion shows
that the element already belongs to the original field.
-/

namespace ValuationTheory.Henselian

open Polynomial

private theorem exists_algebraMap_eq_of_normal_of_approximable
    {K L : Type*} [NormedField K] [NormedField L]
    [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]
    [FiniteDimensional K L] [Normal K L]
    [HenselianRing (NormedField.valuation (K := K)).valuationSubring
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring)]
    (a : L) (ha : IsSeparable K a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖a - algebraMap K L k‖ < ε) :
    ∃ k : K, algebraMap K L k = a := by
  have hfixed (σ : L ≃ₐ[K] L) : σ a = a := by
    by_contra hne
    have hpos : 0 < ‖σ a - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := happrox ‖σ a - a‖ hpos
    have hnorm : ‖σ a - algebraMap K L k‖ = ‖a - algebraMap K L k‖ := by
      calc
        ‖σ a - algebraMap K L k‖ = ‖σ (a - algebraMap K L k)‖ := by
          rw [map_sub, σ.commutes]
        _ = ‖a - algebraMap K L k‖ :=
          norm_algEquiv_eq_of_henselianRing σ (a - algebraMap K L k)
    have hle : ‖σ a - a‖ ≤ ‖a - algebraMap K L k‖ := by
      calc
        ‖σ a - a‖ = ‖(σ a - algebraMap K L k) + (algebraMap K L k - a)‖ := by
          rw [sub_add_sub_cancel]
        _ ≤ max ‖σ a - algebraMap K L k‖ ‖algebraMap K L k - a‖ :=
          IsUltrametricDist.norm_add_le_max
            (σ a - algebraMap K L k) (algebraMap K L k - a)
        _ = ‖a - algebraMap K L k‖ := by rw [hnorm, norm_sub_rev, max_self]
    exact (not_lt_of_ge hle) hk
  have hmem : a ∈ (⊥ : Subalgebra K L) := by
    by_contra hnot
    obtain ⟨b, hne, hconj⟩ :=
      (notMem_iff_exists_ne_and_isConjRoot ha
        (Normal.splits (inferInstance : Normal K L) a)).mp hnot
    obtain ⟨σ, hσ⟩ := isConjRoot_iff_exists_algEquiv.mp hconj
    exact hne (σ.injective ((hfixed σ).trans hσ.symm))
  exact Algebra.mem_bot.mp hmem

private theorem exists_algebraMap_eq_of_isAlgClosed_of_approximable
    {K Ω : Type*} [NormedField K] [NormedField Ω]
    [IsUltrametricDist K] [IsUltrametricDist Ω] [NormedAlgebra K Ω] [IsAlgClosed Ω]
    [HenselianRing (NormedField.valuation (K := K)).valuationSubring
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring)]
    (a : Ω) (ha : IsSeparable K a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖a - algebraMap K Ω k‖ < ε) :
    ∃ k : K, algebraMap K Ω k = a := by
  let N : IntermediateField K Ω := IntermediateField.adjoin K ((minpoly K a).rootSet Ω)
  have hsplits : ((minpoly K a).map (algebraMap K Ω)).Splits := IsAlgClosed.splits _
  have : IsSplittingField K N (minpoly K a) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplits
  have : FiniteDimensional K N := IsSplittingField.finiteDimensional N (minpoly K a)
  have : Normal K N := Normal.of_isSplittingField (minpoly K a)
  have haN : a ∈ N := IntermediateField.subset_adjoin K ((minpoly K a).rootSet Ω)
    (mem_rootSet.mpr ⟨minpoly.ne_zero ha.isIntegral, minpoly.aeval K a⟩)
  let aN : N := ⟨a, haN⟩
  have haNsep : IsSeparable K aN :=
    (isSeparable_map_iff N.val N.val.injective).mp ha
  have happroxN : ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖aN - algebraMap K N k‖ < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := happrox ε hε
    exact ⟨k, hk⟩
  obtain ⟨k, hk⟩ := exists_algebraMap_eq_of_normal_of_approximable aN haNsep happroxN
  exact ⟨k, congrArg (fun x : N => (x : Ω)) hk⟩

private theorem exists_algebraMap_eq_of_complete_of_approximable
    {K D : Type*} [NormedField K] [NontriviallyNormedField D]
    [IsUltrametricDist K] [IsUltrametricDist D] [NormedAlgebra K D] [CompleteSpace D]
    [HenselianRing (NormedField.valuation (K := K)).valuationSubring
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring)]
    (a : D) (ha : IsSeparable K a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖a - algebraMap K D k‖ < ε) :
    ∃ k : K, algebraMap K D k = a := by
  let Ω := AlgebraicClosure D
  let : NormedField Ω := spectralNorm.normedField D Ω
  let : NormedAlgebra D Ω := spectralNorm.normedAlgebra D Ω
  let : NormedAlgebra K Ω := NormedAlgebra.restrictScalars K D Ω
  have : IsScalarTower K D Ω := IsScalarTower.of_algebraMap_eq (fun k : K => rfl)
  have : IsUltrametricDist Ω := IsUltrametricDist.of_normedAlgebra D
  let j : D →ₐ[K] Ω := IsScalarTower.toAlgHom K D Ω
  have hasep : IsSeparable K (j a) := ha.map j j.injective
  have happroxΩ : ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖j a - algebraMap K Ω k‖ < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := happrox ε hε
    refine ⟨k, ?_⟩
    have hnorm : ‖j a - algebraMap K Ω k‖ = ‖a - algebraMap K D k‖ := by
      change ‖algebraMap D Ω a - algebraMap K Ω k‖ = ‖a - algebraMap K D k‖
      rw [IsScalarTower.algebraMap_apply K D Ω, ← map_sub, norm_algebraMap']
    rw [hnorm]
    exact hk
  obtain ⟨k, hk⟩ :=
    exists_algebraMap_eq_of_isAlgClosed_of_approximable (j a) hasep happroxΩ
  refine ⟨k, j.injective ?_⟩
  exact (j.commutes k).trans hk

/-- A nonarchimedean Henselian normed field is separably algebraically closed
in its completion. Completeness of the original field is not required. -/
theorem exists_completion_eq_of_isSeparable
    {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
    [HenselianRing (NormedField.valuation (K := K)).valuationSubring
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring)]
    (a : UniformSpace.Completion K) (ha : IsSeparable K a) :
    ∃ k : K, (k : UniformSpace.Completion K) = a := by
  let D := UniformSpace.Completion K
  let : NontriviallyNormedField D :=
    { (inferInstance : NormedField D) with
      non_trivial := by
        obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm K
        exact ⟨(k : D), (UniformSpace.Completion.norm_coe k).symm ▸ hk⟩ }
  have : IsUltrametricDist D := IsUltrametricDist.of_normedAlgebra K
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ k : K, ‖a - algebraMap K D k‖ < ε := by
    intro ε hε
    obtain ⟨k, hk⟩ := (UniformSpace.Completion.denseRange_coe (α := K)).exists_dist_lt a hε
    refine ⟨k, ?_⟩
    change ‖a - (k : D)‖ < ε
    simpa only [dist_eq_norm] using hk
  exact exists_algebraMap_eq_of_complete_of_approximable a ha happrox

end ValuationTheory.Henselian
