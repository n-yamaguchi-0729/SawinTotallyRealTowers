/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Data.Int.WithZero
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Norm.Basic

/-!
# The field norm as a valuation on a finite extension

For a complete rank-one valued field, the field norm gives a valuation on
any finite field extension. The strong triangle inequality follows from the
actual spectral absolute-value extension. Separability is not needed.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

open AlgebraicNumberTheory.Valuations

universe u v w

private theorem normAbsoluteValue_complete
    (K : Type u) [NormedField K] [CompleteSpace K] :
    IsCompleteForAbsoluteValue (NormedField.toAbsoluteValue K) := by
  apply (absoluteValueCompleteness_completeSpace_withAbs_iff_complete
    (NormedField.toAbsoluteValue K)).1
  let e : WithAbs (NormedField.toAbsoluteValue K) ≃ᵢ K :=
    { toEquiv := (WithAbs.equiv (NormedField.toAbsoluteValue K)).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub, WithAbs.norm_eq_apply_ofAbs,
          WithAbs.ofAbs_sub]
        rfl }
  exact e.completeSpace

section General

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable {Γ : Type v} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
variable [(Valued.v : _root_.Valuation K Γ).RankOne] [CompleteSpace K]

/-- The field norm satisfies the valuation triangle inequality over a complete
rank-one valued base, including for inseparable finite extensions. -/
theorem valuation_norm_add_le_max (x y : L) :
    (Valued.v : _root_.Valuation K Γ) (Algebra.norm K (x + y)) ≤
      max (Valued.v (Algebra.norm K x)) (Valued.v (Algebra.norm K y)) := by
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K Γ
  let a : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have ha : a.IsNontrivial := by
    obtain ⟨z, hz⟩ := NormedField.exists_one_lt_norm K
    refine ⟨z, ?_, ne_of_gt hz⟩
    exact norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hz))
  have hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    LubinTate.Valuations.nonarchimedean_of_strong_triangle a
      (Valued.isNonarchimedean_norm K Γ)
  have h := finiteNormExtension_finite_normFormulaValue_strong_triangle
    a (normAbsoluteValue_complete K) hn ha x y
  have hd : 0 < 1 / (Module.finrank K L : ℝ) :=
    one_div_pos.mpr (by exact_mod_cast Module.finrank_pos (R := K) (M := L))
  rw [le_max_iff] at h ⊢
  rcases h with hx | hy
  · left
    apply (Valued.toNormedField.norm_le_iff (L := K) (Γ₀ := Γ)).1
    exact (Real.rpow_le_rpow_iff
      (norm_nonneg (Algebra.norm K (x + y)))
      (norm_nonneg (Algebra.norm K x)) hd).1 hx
  · right
    apply (Valued.toNormedField.norm_le_iff (L := K) (Γ₀ := Γ)).1
    exact (Real.rpow_le_rpow_iff
      (norm_nonneg (Algebra.norm K (x + y)))
      (norm_nonneg (Algebra.norm K y)) hd).1 hy

/-- The valuation obtained by applying the base valuation to the actual
field norm. Its restriction is the degree-th power of the base valuation. -/
def finiteNormValuation : _root_.Valuation L Γ where
  toFun x := (Valued.v : _root_.Valuation K Γ) (Algebra.norm K x)
  map_zero' := by rw [Algebra.norm_zero, map_zero]
  map_one' := by rw [map_one, map_one]
  map_mul' x y := by rw [map_mul, map_mul]
  map_add_le_max' := valuation_norm_add_le_max

/-- Restriction of the norm valuation to the base field. -/
theorem finiteNormValuation_algebraMap (x : K) :
    finiteNormValuation (K := K) (L := L) (Γ := Γ) (algebraMap K L x) =
      (Valued.v : _root_.Valuation K Γ) x ^ Module.finrank K L := by
  change Valued.v (Algebra.norm K (algebraMap K L x)) = _
  rw [Algebra.norm_algebraMap, map_pow]

/-- The actual norm valuation extends the original valuation in the
valuation-ring sense. -/
theorem finiteNormValuation_hasExtension :
    (Valued.v : _root_.Valuation K Γ).HasExtension
      (finiteNormValuation (K := K) (L := L) (Γ := Γ)) := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext x
  change finiteNormValuation (K := K) (L := L) (Γ := Γ)
      (algebraMap K L x) ≤ 1 ↔ (Valued.v : _root_.Valuation K Γ) x ≤ 1
  rw [finiteNormValuation_algebraMap]
  exact pow_le_one_iff_of_nonneg zero_le
    (Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L)))

/-- The norm valuation is nontrivial because its restriction is a positive
power of the nontrivial base valuation. -/
theorem finiteNormValuation_isNontrivial :
    (finiteNormValuation (K := K) (L := L) (Γ := Γ)).IsNontrivial := by
  obtain ⟨x, hx0, hx1⟩ :=
    _root_.Valuation.RankOne.nontrivial (Valued.v : _root_.Valuation K Γ)
  refine ⟨⟨algebraMap K L x, ?_, ?_⟩⟩
  · rw [finiteNormValuation_algebraMap]
    exact pow_ne_zero _ hx0
  · rw [finiteNormValuation_algebraMap]
    exact fun h => hx1 ((pow_eq_one_iff_of_nonneg zero_le
      (Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L)))).1 h)

end General

/-- In the integer-valued case the actual finite-extension norm valuation is
discrete: its nonzero value group is a nontrivial subgroup of the integers. -/
theorem finiteNormValuation_isRankOneDiscrete
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Valued K (WithZero (Multiplicative ℤ))]
    [(Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ))).RankOne]
    [CompleteSpace K] :
    (finiteNormValuation (K := K) (L := L)
      (Γ := WithZero (Multiplicative ℤ))).IsRankOneDiscrete := by
  let vL : _root_.Valuation L (WithZero (Multiplicative ℤ)) :=
    finiteNormValuation (K := K) (L := L)
  let : vL.IsNontrivial := finiteNormValuation_isNontrivial
  let : IsCyclic (MonoidWithZeroHom.valueGroup (.ofClass vL)) :=
    Subgroup.isCyclic_of_le (show
      MonoidWithZeroHom.valueGroup (.ofClass vL) ≤ ⊤ from le_top)
  exact _root_.Valuation.IsRankOneDiscrete.mk' vL

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
