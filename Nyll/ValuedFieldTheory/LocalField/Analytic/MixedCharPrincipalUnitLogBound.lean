/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.LogDenominatorLowerBound
import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ValuationLimit
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharLogTermBound
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog

/-!
# A lower bound for valuations in the principal-unit logarithm image

The integer sequence `n - e * v_p(n)`, for positive `n`, has an attained
minimum. Every nonzero principal-unit logarithm has integer valuation at
least that minimum. The bound is uniform over all principal units, including
when the residue field is infinite.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The exact denominator minimum bounds every nonzero logarithmic value. -/
theorem exists_principalUnitLog_denominator_min_bound
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    ∃ m : ℕ,
      (∀ n : ℕ,
        ((m + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
            (padicValNat p (m + 1) : ℤ) ≤
          ((n + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
            (padicValNat p (n + 1) : ℤ)) ∧
      ∀ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
        ∀ hu : (principalUnitLogOfMixedChar v p u).toAdd ≠ 0,
          ((m + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
              (padicValNat p (m + 1) : ℤ) ≤
            (ofWithZeroValuation v).val
              (Units.mk0 (principalUnitLogOfMixedChar v p u).toAdd hu) := by
  obtain ⟨m, hm⟩ := exists_log_denominator_min p (v.residueRamificationIndex p)
  refine ⟨m, hm, ?_⟩
  intro u hu
  let b : ℤ := ((m + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
    (padicValNat p (m + 1) : ℤ)
  let x : K := principalUnitSubOneOfWithZeroValuation v u
  have hx : v x < 1 := principalUnitSubOne_val_lt_one_ofWithZeroValuation v u
  have hn : ∀ n : ℕ, ((n + 1 : ℕ) : K) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hpartial : ∀ N : ℕ,
      v (logOnePlusPartialSumField x hn N) ≤ WithZero.exp (-b) := by
    intro N
    apply v.map_sum_le
    intro n _
    refine (valuation_signedLogSeriesTermField_le_mixedChar v p x hx n).trans ?_
    exact WithZero.exp_le_exp.mpr (neg_le_neg (hm n))
  have hlogbound :
      v (logOnePlusSeriesFieldOfWithZeroValuation v x hn) ≤ WithZero.exp (-b) :=
    valuation_limit_le_of_tendsto_of_eventually_le v
      (tendsto_logOnePlusPartialSumField_ofWithZeroValuation_scaled_of_lt_one
        (p := p) v (v.residueRamificationIndex p) x hn
        (fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
          (n + 1) (Nat.succ_ne_zero n)) hx
        (ValuationTheory.DiscreteValuationField.Valuation.completeSpace_ofWithZeroValuation v))
      (Filter.Eventually.of_forall hpartial)
  have hvalue : logOnePlusSeriesFieldOfWithZeroValuation v x hn =
      (principalUnitLogOfMixedChar v p u).toAdd := rfl
  rw [hvalue] at hlogbound
  have hlog := (WithZero.log_le_iff_le_exp ((v.ne_zero_iff).mpr hu)).mpr hlogbound
  change b ≤ -WithZero.log (v (principalUnitLogOfMixedChar v p u).toAdd)
  omega

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
