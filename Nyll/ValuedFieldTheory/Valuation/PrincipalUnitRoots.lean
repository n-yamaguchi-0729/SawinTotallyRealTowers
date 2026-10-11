/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Prime-power roots of principal units

In residue characteristic `p`, if a `p`-power of a field element is a
principal unit, so is the element. This uses neither discreteness nor
completeness of the valuation, and does not require the residue field
to be perfect.
-/

namespace Valuation

universe u v

/-- A prime-power root of a principal unit is itself a principal unit,
for an arbitrary ordered value group. -/
theorem map_eq_one_and_sub_one_lt_one_of_prime_pow
    {K : Type u} {Γ : Type v} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (s : ℕ) (y : K) (hy : v (y ^ (p ^ s) - 1) < 1) :
    v y = 1 ∧ v (y - 1) < 1 := by
  have hn : p ^ s ≠ 0 := pow_ne_zero s (Fact.out : p.Prime).ne_zero
  have hypow : v (y ^ (p ^ s)) = 1 := by
    have hsub : v (y ^ (p ^ s) - 1) < v (1 : K) := by
      rwa [map_one]
    simpa only [map_one] using v.map_eq_of_sub_lt hsub
  have hyval : v y = 1 :=
    (pow_eq_one_iff_of_nonneg (zero_le : 0 ≤ v y) hn).mp
      (by simpa only [map_pow] using hypow)
  let a : v.valuationSubring := ⟨y, by change v y ≤ 1; exact hyval.le⟩
  have hmax : a ^ (p ^ s) - 1 ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
    apply v.mem_maximalIdeal_iff.mpr
    change v (y ^ (p ^ s) - 1) < 1
    exact hy
  have hrespow : (IsLocalRing.residue v.valuationSubring a) ^ (p ^ s) = 1 := by
    have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hmax
    rwa [_root_.map_sub, _root_.map_pow, _root_.map_one, sub_eq_zero] at hz
  have hres : IsLocalRing.residue v.valuationSubring a = 1 := by
    simpa only [pow_one] using
      (ExpChar.pow_prime_pow_mul_eq_one_iff p s 1
        (IsLocalRing.residue v.valuationSubring a)).mp
        (by simpa only [mul_one] using hrespow)
  have hmax' : a - 1 ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
    apply (IsLocalRing.residue_eq_zero_iff _).mp
    rw [_root_.map_sub, hres, _root_.map_one, sub_self]
  refine ⟨hyval, ?_⟩
  have hlt := v.mem_maximalIdeal_iff.mp hmax'
  change v (y - 1) < 1 at hlt
  exact hlt

end Valuation
