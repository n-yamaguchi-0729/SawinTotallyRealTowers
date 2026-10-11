/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.Extension
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Finset.Max

/-!
# Residue fields of finite valued extensions

A linearly independent family in the residue extension lifts to a linearly
independent family upstairs: divide a proposed relation by a coefficient of
maximal valuation and reduce. This proves finite residue degree without
separability, completeness, or discreteness assumptions.
-/

noncomputable section
namespace Valuation
open IsLocalRing
variable {K L Γ Δ : Type*} [Field K] [Field L] [Algebra K L]
variable [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
variable (v : Valuation K Γ) (w : Valuation L Δ) [v.HasExtension w]

/-- Linearly independent residues have linearly independent representatives. -/
theorem linearIndependent_lifts_residue {ι : Type*}
    (b : ι → w.valuationSubring)
    (hb : LinearIndependent (ResidueField v.valuationSubring)
      (fun i => residue w.valuationSubring (b i))) :
    LinearIndependent K (fun i => (b i : L)) := by
  classical
  apply linearIndependent_iff'.2
  intro s g hg i hi
  by_contra hgi
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun i => v (g i)) ⟨i, hi⟩
  have hgj : g j ≠ 0 := by
    intro hj0
    have h := hmax i hi
    rw [hj0, map_zero, le_zero_iff] at h
    exact hgi (v.zero_iff.1 h)
  let c : s → v.valuationSubring := fun i =>
    ⟨g i / g j, by
      change v (g i / g j) ≤ 1
      rw [map_div₀, div_le_one₀ ((v.pos_iff).2 hgj)]
      exact hmax i i.2⟩
  have hsum : ∑ i : s, algebraMap v.valuationSubring w.valuationSubring (c i) * b i = 0 := by
    apply Subtype.ext
    change w.valuationSubring.subtype (∑ i : s,
      algebraMap v.valuationSubring w.valuationSubring (c i) * b i) =
      w.valuationSubring.subtype 0
    simp only [map_sum, map_mul, map_zero]
    change ∑ i : s, algebraMap K L (g i / g j) * (b i : L) = 0
    calc
      _ = (algebraMap K L (g j))⁻¹ * ∑ i : s, g i • (b i : L) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_div₀, Algebra.smul_def]
        simp only [div_eq_mul_inv, mul_assoc, mul_comm (algebraMap K L (g i))
          ((algebraMap K L (g j))⁻¹)]
      _ = 0 := by
        rw [Finset.sum_coe_sort s (fun i => g i • (b i : L)), hg, mul_zero]
  have hres : ∑ i : s, residue v.valuationSubring (c i) •
      residue w.valuationSubring (b i) = 0 := by
    have h := congrArg (residue w.valuationSubring) hsum
    simp only [map_sum, map_mul, map_zero] at h
    simpa only [Algebra.smul_def,
      HasExtension.algebraMap_residue_eq_residue_algebraMap] using h
  have hbind : LinearIndependent (ResidueField v.valuationSubring)
      (fun i : s => residue w.valuationSubring (b i)) :=
    hb.comp (fun i : s => (i : ι)) Subtype.val_injective
  have hjres := Fintype.linearIndependent_iff.mp hbind
    (fun i => residue v.valuationSubring (c i)) hres ⟨j, hj⟩
  have hcj : c ⟨j, hj⟩ = 1 := by
    apply Subtype.ext
    exact div_self hgj
  rw [hcj, map_one] at hjres
  exact one_ne_zero hjres

/-- A finite valued extension has finite residue degree. -/
theorem finiteDimensional_residueField [FiniteDimensional K L] :
    FiniteDimensional (ResidueField v.valuationSubring) (ResidueField w.valuationSubring) := by
  classical
  let b := Module.Basis.ofVectorSpace (ResidueField v.valuationSubring)
    (ResidueField w.valuationSubring)
  choose t ht using fun i => (residue_surjective (R := w.valuationSubring)) (b i)
  have hind : LinearIndependent (ResidueField v.valuationSubring)
      (fun i => residue w.valuationSubring (t i)) := by
    simpa only [ht] using b.linearIndependent
  have : Finite (Module.Basis.ofVectorSpaceIndex (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring)) := (linearIndependent_lifts_residue v w t hind).finite
  exact b.finiteDimensional_of_finite
end Valuation
