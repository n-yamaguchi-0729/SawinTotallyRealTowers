/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Int.WithZero
import Mathlib.Data.Int.LeastGreatest

/-!
# Square roots and first-order principal units in dyadic valued fields

Hensel's simple-root theorem bounds the precision of a nonsquare near one.
For integer-valued valuations, a principal unit of valuation-one difference
from one cannot be a square when the value of two is less than one.
-/

namespace ValuationTheory

/-- The substitution b = 1 + 2z reduces the square-root problem to a monic
polynomial with derivative one at its residual root. -/
theorem exists_sq_eq_of_valuation_sub_one_lt_two_sq
    {K Γ : Type*} [Field K] [CharZero K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (a : K) (ha : v (a - 1) < v (2 : K) ^ 2) :
    ∃ b : K, b ^ 2 = a := by
  have htwo : 0 < v (2 : K) := lt_of_le_of_ne zero_le
    (Ne.symm ((Valuation.ne_zero_iff v).mpr (by norm_num)))
  have hcval : v ((1 - a) / 4) < 1 := by
    rw [v.map_div, v.map_sub_swap, show (4 : K) = 2 ^ 2 by norm_num, map_pow]
    exact (div_lt_one₀ (pow_pos htwo 2)).mpr ha
  let c : v.valuationSubring := ⟨(1 - a) / 4, hcval.le⟩
  let f : Polynomial v.valuationSubring :=
    Polynomial.X ^ 2 + (Polynomial.X + Polynomial.C c)
  have hf : f.Monic := by
    apply Polynomial.monic_X_pow_add
    rw [Polynomial.degree_X_add_C]
    norm_num
  have hc : c ∈ IsLocalRing.maximalIdeal v.valuationSubring :=
    (v.mem_maximalIdeal_iff).mpr hcval
  have hroot : f.eval 0 ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
    simpa only [f, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, zero_pow (by decide : 2 ≠ 0), zero_add] using hc
  have hderiv : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal v.valuationSubring)
      (f.derivative.eval 0)) := by
    norm_num [f, Polynomial.derivative_add, Polynomial.derivative_pow]
  obtain ⟨z, hz, _⟩ := HenselianRing.is_henselian f hf 0 hroot hderiv
  have hzeval : z ^ 2 + (z + c) = 0 := by
    simpa only [f, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C] using Polynomial.IsRoot.def.mp hz
  have hz' := congrArg ((↑) : v.valuationSubring → K) hzeval
  change (z : K) ^ 2 + ((z : K) + (1 - a) / 4) = 0 at hz'
  refine ⟨1 + 2 * (z : K), ?_⟩
  field_simp at hz'
  linear_combination hz'

private theorem le_exp_neg_one_of_lt_one
    {x : WithZero (Multiplicative ℤ)} (hx : x < 1) :
    x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hzero : x = 0
  · rw [hzero]
    exact zero_le
  · lift x to Multiplicative ℤ using hzero
    have hx' : x < 1 := WithZero.coe_lt_coe.mp hx
    apply WithZero.coe_le_coe.mpr
    change Multiplicative.toAdd x < 0 at hx'
    change Multiplicative.toAdd x ≤ -1
    omega

/-- A first-order principal unit is not a square in residue characteristic two.
Only the inequality for the value of two is needed. -/
theorem not_isSquare_of_valuation_sub_one_eq_exp_neg_one
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (h2 : v (2 : K) < 1)
    {a : K} (ha : v (a - 1) = WithZero.exp (-1 : ℤ)) :
    ¬ IsSquare a := by
  rintro ⟨y, rfl⟩
  have hpoly : y * y - 1 = (y - 1) ^ 2 + 2 * (y - 1) := by ring
  by_cases hy : v (y - 1) < 1
  · have hybound := le_exp_neg_one_of_lt_one hy
    have h2bound := le_exp_neg_one_of_lt_one h2
    have hsq : v ((y - 1) ^ 2) ≤ WithZero.exp (-2 : ℤ) := by
      rw [map_pow, pow_two]
      simpa only [← WithZero.exp_add, show (-1 : ℤ) + -1 = -2 by norm_num]
        using mul_le_mul' hybound hybound
    have hmul : v (2 * (y - 1)) ≤ WithZero.exp (-2 : ℤ) := by
      rw [map_mul]
      simpa only [← WithZero.exp_add, show (-1 : ℤ) + -1 = -2 by norm_num]
        using mul_le_mul' h2bound hybound
    have hle := (v.map_add ((y - 1) ^ 2) (2 * (y - 1))).trans (max_le hsq hmul)
    rw [← hpoly, ha] at hle
    have hle' := WithZero.coe_le_coe.mp hle
    change (-1 : ℤ) ≤ -2 at hle'
    omega
  · have hyone : 1 ≤ v (y - 1) := le_of_not_gt hy
    have hpos : 0 < v (y - 1) := zero_lt_one.trans_le hyone
    have hlt : v (2 * (y - 1)) < v ((y - 1) ^ 2) := by
      rw [map_mul, map_pow, pow_two]
      exact mul_lt_mul_of_pos_right (h2.trans_le hyone) hpos
    have heq : v (y * y - 1) = v (y - 1) * v (y - 1) := by
      rw [hpoly, v.map_add_eq_of_lt_left hlt, map_pow, pow_two]
    have hge : 1 ≤ v (y * y - 1) := by
      rw [heq]
      simpa only [one_mul] using mul_le_mul' hyone hyone
    rw [ha] at hge
    have hge' := WithZero.coe_le_coe.mp hge
    change (0 : ℤ) ≤ -1 at hge'
    omega


/-- A nonsquare has a square multiple closest to one among multipliers of value one. -/
theorem exists_minimal_valuation_squareClass_difference
    {K : Type*} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (a : Kˣ) (hns : ¬ IsSquare (a : K)) :
    ∃ c : Kˣ, v (c : K) = 1 ∧
      ∀ d : Kˣ, v (d : K) = 1 →
        v ((a : K) * (c : K) ^ 2 - 1) ≤ v ((a : K) * (d : K) ^ 2 - 1) := by
  have hns' (c : Kˣ) : ¬ IsSquare ((a : K) * (c : K) ^ 2) := by
    rintro ⟨y, hy⟩
    apply hns
    refine ⟨y / (c : K), ?_⟩
    field_simp
    linear_combination hy
  have hbound (c : Kˣ) :
      v (2 : K) ^ 2 ≤ v ((a : K) * (c : K) ^ 2 - 1) := by
    apply le_of_not_gt
    intro hsmall
    obtain ⟨b, hb⟩ := exists_sq_eq_of_valuation_sub_one_lt_two_sq
      v ((a : K) * (c : K) ^ 2) hsmall
    apply hns' c
    exact ⟨b, by rw [← hb, pow_two]⟩
  have htwo : 0 < v (2 : K) := lt_of_le_of_ne zero_le
    (Ne.symm ((Valuation.ne_zero_iff v).mpr (by norm_num)))
  have hne (c : Kˣ) : v ((a : K) * (c : K) ^ 2 - 1) ≠ 0 :=
    ne_of_gt ((pow_pos htwo 2).trans_le (hbound c))
  have hlogbound (c : Kˣ) :
      2 * WithZero.log (v (2 : K)) ≤ WithZero.log (v ((a : K) * (c : K) ^ 2 - 1)) := by
    have h := hbound c
    rw [← WithZero.exp_log htwo.ne', pow_two, ← WithZero.exp_add,
      ← WithZero.exp_log (hne c)] at h
    have h' := WithZero.coe_le_coe.mp h
    change WithZero.log (v (2 : K)) + WithZero.log (v (2 : K)) ≤
      WithZero.log (v ((a : K) * (c : K) ^ 2 - 1)) at h'
    omega
  obtain ⟨n, ⟨c, hc, hcn⟩, hn⟩ := Int.exists_least_of_bdd
    (P := fun n => ∃ c : Kˣ, v (c : K) = 1 ∧
      WithZero.log (v ((a : K) * (c : K) ^ 2 - 1)) = n)
    (by
      refine ⟨2 * WithZero.log (v (2 : K)), ?_⟩
      rintro n ⟨c, _hc, rfl⟩
      exact hlogbound c)
    ⟨WithZero.log (v ((a : K) * ((1 : Kˣ) : K) ^ 2 - 1)), 1, v.map_one, rfl⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  have hcd : WithZero.log (v ((a : K) * (c : K) ^ 2 - 1)) ≤
      WithZero.log (v ((a : K) * (d : K) ^ 2 - 1)) := by
    rw [hcn]
    exact hn _ ⟨d, hd, rfl⟩
  have hvalues : WithZero.exp (WithZero.log (v ((a : K) * (c : K) ^ 2 - 1))) ≤
      WithZero.exp (WithZero.log (v ((a : K) * (d : K) ^ 2 - 1))) :=
    WithZero.coe_le_coe.mpr hcd
  simpa only [WithZero.exp_log (hne c), WithZero.exp_log (hne d)] using hvalues

end ValuationTheory
