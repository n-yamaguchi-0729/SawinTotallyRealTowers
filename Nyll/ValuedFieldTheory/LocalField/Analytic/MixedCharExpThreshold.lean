/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The exponential threshold on `p²` times the valuation ring

The value of the residue prime supplies the strict ramified convergence bound.
No completeness or normalization of the integer-valued valuation is needed.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Every nonzero element of `p²` times the valuation ring lies strictly above
the ramified exponential threshold. -/
theorem exp_threshold_natCast_sq_mul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (a : v.valuationSubring) (hx : (p : K) ^ 2 * (a : K) ≠ 0) :
    (v.residueRamificationIndex p : ℝ) / ((p : ℝ) - 1) <
      ((ofWithZeroValuation v).val (Units.mk0 ((p : K) ^ 2 * (a : K)) hx) : ℝ) := by
  have hva : v (a : K) ≤ 1 := a.property
  have hvbound :
      v ((p : K) ^ 2 * (a : K)) ≤
        WithZero.exp (-(2 * (v.residueRamificationIndex p : ℤ))) := by
    calc
      v ((p : K) ^ 2 * (a : K)) = v (p : K) ^ 2 * v (a : K) := by
        rw [v.map_mul, _root_.map_pow]
      _ ≤ v (p : K) ^ 2 * 1 := mul_le_mul_of_nonneg_left hva zero_le
      _ = WithZero.exp (-(2 * (v.residueRamificationIndex p : ℤ))) := by
        rw [mul_one, v.natCast_residueChar_eq_exp_neg p, pow_two, ← WithZero.exp_add]
        simp only [two_mul, neg_add]
  have hlog :=
    (WithZero.log_le_iff_le_exp ((v.ne_zero_iff).mpr hx)).mpr hvbound
  have hval :
      2 * (v.residueRamificationIndex p : ℤ) ≤
        (ofWithZeroValuation v).val (Units.mk0 ((p : K) ^ 2 * (a : K)) hx) := by
    change 2 * (v.residueRamificationIndex p : ℤ) ≤
      -WithZero.log (v ((p : K) ^ 2 * (a : K)))
    linarith
  have hvalReal :
      2 * (v.residueRamificationIndex p : ℝ) ≤
        ((ofWithZeroValuation v).val (Units.mk0 ((p : K) ^ 2 * (a : K)) hx) : ℝ) := by
    exact_mod_cast hval
  have he : (0 : ℝ) < (v.residueRamificationIndex p : ℝ) := by
    exact_mod_cast v.residueRamificationIndex_pos p
  have hp : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).two_le
  have hdiv : (v.residueRamificationIndex p : ℝ) / ((p : ℝ) - 1) ≤
      (v.residueRamificationIndex p : ℝ) := div_le_self he.le (by linarith)
  linarith

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
