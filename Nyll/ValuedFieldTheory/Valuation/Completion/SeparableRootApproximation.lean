/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Normed.Field.Krasner
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Approximating separable generators over a dense subfield

Approximate the minimal polynomial by a monic polynomial over the dense
subfield. Continuity of roots produces a nearby root in the algebraic
closure, and Krasner's lemma places the original generator in its adjoin.
-/

namespace ValuationTheory.Completion

open Polynomial
open scoped Topology

private theorem exists_pos_le_norm_sub_conjugate
    {A Ω : Type*} [Field A] [NormedField Ω] [Algebra A Ω]
    (α : Ω) (hα : IsIntegral A α) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ α' : Ω, IsConjRoot A α α' → α ≠ α' →
      δ ≤ ‖α - α'‖ := by
  let s : Set Ω := (minpoly A α).rootSet Ω \ {α}
  have hsfinite : s.Finite := ((minpoly A α).rootSet_finite Ω).sdiff
  have hclosed : IsClosed s := hsfinite.isClosed
  have hαmem : α ∈ sᶜ := fun h => h.2 rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hclosed.isOpen_compl α hαmem
  refine ⟨δ, hδ, ?_⟩
  intro α' hconj hne
  apply le_of_not_gt
  intro hlt
  have hroot : α' ∈ (minpoly A α).rootSet Ω :=
    (isConjRoot_iff_mem_minpoly_rootSet hα).mp hconj
  have hmem : α' ∈ s := ⟨hroot, fun heq => hne heq.symm⟩
  apply (hball ?_) hmem
  simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hlt

private theorem exists_monic_root_with_adjoin_containment_of_normed
    {K A Ω : Type*} [Field K] [NontriviallyNormedField A]
    [CompleteSpace A] [IsUltrametricDist A] [NormedField Ω]
    [Algebra K A] [NormedAlgebra A Ω] [Algebra K Ω] [IsScalarTower K A Ω]
    [IsAlgClosed Ω] [Algebra.IsAlgebraic A Ω]
    (hd : DenseRange (algebraMap K A)) (α : Ω) (hα : IsSeparable A α) :
    ∃ g : K[X], ∃ β : Ω, g.Monic ∧
      g.natDegree = (minpoly A α).natDegree ∧ g.aeval β = 0 ∧
        α ∈ IntermediateField.adjoin A ({β} : Set Ω) := by
  let f : A[X] := minpoly A α
  have hfmonic : f.Monic := minpoly.monic hα.isIntegral
  have hfpos : 0 < f.natDegree := minpoly.natDegree_pos hα.isIntegral
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_le_norm_sub_conjugate α hα.isIntegral
  let ε : ℝ := (δ / max ‖α‖ 1) ^ f.natDegree / (f.natDegree + 1)
  have hm : 0 < max ‖α‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right ‖α‖ 1)
  have hn : (0 : ℝ) < f.natDegree + 1 := by positivity
  have hε : 0 < ε := div_pos (pow_pos (div_pos hδ hm) f.natDegree) hn
  obtain ⟨g, hgmonic, hgdegree, hgcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hd hfmonic hε
  have hgmapdegree : (g.map (algebraMap K A)).natDegree = f.natDegree :=
    (hgmonic.natDegree_map (algebraMap K A)).trans hgdegree.symm
  obtain ⟨β, hβroot, hβdist⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
    hε (minpoly.aeval A α) hfmonic (hgmonic.map (algebraMap K A)) hgmapdegree
    hgcoeff (IsAlgClosed.splits
      ((g.map (algebraMap K A)).map (algebraMap A Ω)))
  have hbound :
      ((f.natDegree + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ * max ‖α‖ 1 = δ := by
    have hmul : (f.natDegree + 1) * ε = (δ / max ‖α‖ 1) ^ f.natDegree := by
      dsimp only [ε]
      field_simp
    rw [hmul, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (div_pos hδ hm)),
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hfpos)), Real.rpow_one,
      div_mul_cancel₀ δ (ne_of_gt hm)]
  rw [hbound] at hβdist
  have hβmap : (g.map (algebraMap K A)).aeval β = 0 :=
    (mem_aroots.mp hβroot).2
  have hβ : g.aeval β = 0 := by
    rwa [Polynomial.aeval_map_algebraMap] at hβmap
  refine ⟨g, β, hgmonic, hgdegree.symm, hβ, ?_⟩
  exact IsKrasner.krasner hα
    (IsAlgClosed.splits ((minpoly A α).map (algebraMap A Ω)))
    ⟨g.map (algebraMap K A), hgmonic.map (algebraMap K A), hβmap⟩
    (fun α' hconj hne => hβdist.trans_le (hdist α' hconj hne))

/-- A separable element over a complete nonarchimedean field is contained
in the adjoin of a root of a monic polynomial over any dense subfield,
without increasing the degree of its minimal polynomial. -/
theorem exists_monic_root_with_adjoin_containment
    {K A : Type*} [Field K] [NontriviallyNormedField A]
    [CompleteSpace A] [IsUltrametricDist A] [Algebra K A]
    (hd : DenseRange (algebraMap K A)) (α : AlgebraicClosure A)
    (hα : IsSeparable A α) :
    ∃ g : K[X], ∃ β : AlgebraicClosure A, g.Monic ∧
      g.natDegree = (minpoly A α).natDegree ∧ g.aeval β = 0 ∧
        α ∈ IntermediateField.adjoin A ({β} : Set (AlgebraicClosure A)) := by
  let : NormedField (AlgebraicClosure A) := spectralNorm.normedField A (AlgebraicClosure A)
  let : NormedAlgebra A (AlgebraicClosure A) := spectralNorm.normedAlgebra A (AlgebraicClosure A)
  exact exists_monic_root_with_adjoin_containment_of_normed hd α hα

end ValuationTheory.Completion
