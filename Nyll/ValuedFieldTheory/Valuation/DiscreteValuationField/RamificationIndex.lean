/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NatCastValuation
import Mathlib.Algebra.Order.GroupWithZero.Canonical

/-!
# The value of the residue characteristic

For an integer-valued valuation in mixed characteristic, the positive exponent
of the residue prime gives the denominator estimates for logarithm and
exponential series. Neither completeness nor residue-field finiteness is needed.
-/

namespace Valuation

universe u

variable {K : Type u} [Field K]

/-- The nonnegative exponent of the value of a specified residue prime. -/
def residueRamificationIndex (v : Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) : ℕ :=
  (-WithZero.log (v (p : K))).toNat

/-- A residue characteristic has value strictly less than one. -/
theorem natCast_residueChar_lt_one
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ)
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    v (p : K) < 1 := by
  have hres : IsLocalRing.residue v.valuationSubring (p : v.valuationSubring) = 0 := by
    rw [map_natCast, CharP.cast_eq_zero]
  have hmem := (IsLocalRing.residue_eq_zero_iff (p : v.valuationSubring)).mp hres
  have hlt := (Valuation.mem_maximalIdeal_iff (v := v)).mp hmem
  exact_mod_cast hlt

/-- In mixed characteristic the logarithmic value of the residue prime is negative. -/
theorem log_natCast_residueChar_neg [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    WithZero.log (v (p : K)) < 0 := by
  have hne : v (p : K) ≠ 0 :=
    (v.ne_zero_iff).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hlt := (WithZero.log_lt_log hne one_ne_zero).mpr (v.natCast_residueChar_lt_one p)
  simpa only [WithZero.log_one] using hlt

/-- Passing to a natural exponent does not truncate the ramification index. -/
theorem residueRamificationIndex_intCast [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    (v.residueRamificationIndex p : ℤ) = -WithZero.log (v (p : K)) :=
  Int.toNat_of_nonneg (neg_pos.mpr (v.log_natCast_residueChar_neg p)).le

/-- The ramification index of a residue prime in mixed characteristic is positive. -/
theorem residueRamificationIndex_pos [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    0 < v.residueRamificationIndex p := by
  have hpos : (0 : ℤ) < (v.residueRamificationIndex p : ℤ) := by
    rw [v.residueRamificationIndex_intCast p]
    exact neg_pos.mpr (v.log_natCast_residueChar_neg p)
  exact_mod_cast hpos

/-- The actual value of the residue prime is recovered by the constructed exponent. -/
theorem natCast_residueChar_eq_exp_neg [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    v (p : K) = WithZero.exp (-(v.residueRamificationIndex p : ℤ)) := by
  rw [v.residueRamificationIndex_intCast p, neg_neg]
  exact (WithZero.exp_log
    ((v.ne_zero_iff).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))).symm

/-- The denominator valuation formula, with its scale constructed from the valuation. -/
theorem natCast_eq_exp_neg_ramificationIndex_mul_padicValNat [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] (n : ℕ) (hn : n ≠ 0) :
    v (n : K) =
      WithZero.exp (-((v.residueRamificationIndex p : ℤ) * (padicValNat p n : ℤ))) := by
  rw [v.natCast_eq_pow_padicValNat p n hn, v.natCast_residueChar_eq_exp_neg p,
    ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_comm]

end Valuation
