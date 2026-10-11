/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex

/-!
# A uniform bound for mixed-characteristic logarithm terms

If `v(x) < 1`, the integer valuation of the `n`th logarithm term is at least
`n + 1 - e * v_p(n + 1)`. This bound is independent of `x`. The scale `e` and
the denominator values are obtained from the actual residue prime.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- All elements of the open unit ball obey the same logarithm-term estimate. -/
theorem valuation_signedLogSeriesTermField_le_mixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (x : K) (hxv : v x < 1) (n : ℕ) :
    v (signedLogSeriesTermField x
        (fun k => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k)) n) ≤
      WithZero.exp (-(((n + 1 : ℕ) : ℤ) -
        (v.residueRamificationIndex p : ℤ) * (padicValNat p (n + 1) : ℤ))) := by
  by_cases hx : x = 0
  · simp only [hx, signedLogSeriesTermField, logSeriesTermField,
      zero_pow (Nat.succ_ne_zero n), zero_div, mul_zero, v.map_zero]
    exact zero_le
  have hxpos : 0 < (ofWithZeroValuation v).val (Units.mk0 x hx) :=
    ofWithZeroValuation_val_mk0_pos_of_lt_one v hx hxv
  have hxone : (1 : ℤ) ≤ (ofWithZeroValuation v).val (Units.mk0 x hx) := hxpos
  have hn : ((n + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  let t : Kˣ := Units.mk0 x hx ^ (n + 1) / Units.mk0 ((n + 1 : ℕ) : K) hn
  have ht : ((n + 1 : ℕ) : ℤ) -
        (v.residueRamificationIndex p : ℤ) * (padicValNat p (n + 1) : ℤ) ≤
      (ofWithZeroValuation v).val t := by
    rw [show (ofWithZeroValuation v).val t =
      ((n + 1 : ℕ) : ℤ) * (ofWithZeroValuation v).val (Units.mk0 x hx) -
        (v.residueRamificationIndex p : ℤ) * (padicValNat p (n + 1) : ℤ) from
      ofWithZeroValuation_val_pow_div_natCast_scaled v (v.residueRamificationIndex p)
        (Units.mk0 x hx) hn
        (v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
          (n + 1) (Nat.succ_ne_zero n))]
    have hmul := mul_le_mul_of_nonneg_left hxone (Int.natCast_nonneg (n + 1))
    rw [mul_one] at hmul
    exact sub_le_sub_right hmul _
  have hlog : WithZero.log (v (t : K)) ≤
      -(((n + 1 : ℕ) : ℤ) -
        (v.residueRamificationIndex p : ℤ) * (padicValNat p (n + 1) : ℤ)) := by
    change ((n + 1 : ℕ) : ℤ) -
        (v.residueRamificationIndex p : ℤ) * (padicValNat p (n + 1) : ℤ) ≤
      -WithZero.log (v (t : K)) at ht
    omega
  have hbound := WithZero.le_exp_of_log_le hlog
  rw [signedLogSeriesTermField, v.map_mul, v.map_pow, v.map_neg, v.map_one,
    one_pow, one_mul]
  simpa only [t, logSeriesTermField, Units.val_div_eq_div_val,
    Units.val_pow_eq_pow_val, Units.val_mk0] using hbound

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
