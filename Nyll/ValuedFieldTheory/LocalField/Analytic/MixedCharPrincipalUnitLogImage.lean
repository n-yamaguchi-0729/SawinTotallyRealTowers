/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharExpThreshold
import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpComposition

/-!
# The principal-unit logarithm contains the square of the residue prime

Exponentiating `p² a` for an element `a` of the valuation ring produces an
actual principal unit with logarithm `p² a`. The convergence threshold is
proved from the valuation of the residue prime. No normalized uniformizer,
finite residue field, or restriction excluding the prime two is needed.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- Every element of `p² O` is the logarithm of a first principal unit. -/
theorem exists_principalUnit_log_eq_natCast_sq_mul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (a : v.valuationSubring) :
    ∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      (principalUnitLogOfMixedChar v p u).toAdd = (p : K) ^ 2 * (a : K) := by
  let F : ValuationTheory.DiscreteValuationField.CompleteDVF K :=
    completeDVFOfWithZeroValuation v
  let x : K := (p : K) ^ 2 * (a : K)
  let e : ℕ := v.residueRamificationIndex p
  have hnexp : ∀ n : ℕ, (n.factorial : K) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hnlog : ∀ n : ℕ, ((n + 1 : ℕ) : K) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hvexp : ∀ n : ℕ, v (n.factorial : K) =
      WithZero.exp (-((e : ℤ) * (padicValNat p n.factorial : ℤ))) :=
    fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
      n.factorial (Nat.factorial_ne_zero n)
  have hvlog : ∀ n : ℕ, v ((n + 1 : ℕ) : K) =
      WithZero.exp (-((e : ℤ) * (padicValNat p (n + 1) : ℤ))) :=
    fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
      (n + 1) (Nat.succ_ne_zero n)
  have hcomplete : @CompleteSpace K (Valued.mk' v).toUniformSpace :=
    ValuationTheory.DiscreteValuationField.Valuation.completeSpace_ofWithZeroValuation v
  have hthreshold : ∀ hx : x ≠ 0,
      (e : ℝ) / ((p : ℝ) - 1) <
        ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℝ) :=
    fun hx => exp_threshold_natCast_sq_mul v p a hx
  have hxlt : v x < 1 :=
    valuation_lt_one_ofWithZeroValuation_scaled_threshold_real
      (p := p) v e hthreshold
  have hexplt : v (expSeriesFieldOfWithZeroValuation v x hnexp - 1) < 1 := by
    by_cases hx : x = 0
    · rw [hx, expSeriesField_zero_ofWithZeroValuation, sub_self, v.map_zero]
      exact zero_lt_one
    · have hrat : (e : ℚ) / ((p : ℚ) - 1) <
          ((ofWithZeroValuation v).val (Units.mk0 x hx) : ℚ) := by
        exact_mod_cast hthreshold hx
      rw [valuation_expSeriesField_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
        (p := p) v e hx hnexp hvexp hrat hcomplete]
      exact hxlt
  let b : F.valuationSubring :=
    ⟨expSeriesFieldOfWithZeroValuation v x hnexp - 1, hexplt.le⟩
  have hb : b ∈ F.maximalIdeal ^ 1 := by
    rw [pow_one, F.mem_maximalIdeal_iff]
    exact hexplt
  let u : CompleteDVF.higherPrincipalUnitGroup F 1 :=
    CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup
      F (n := 1) le_rfl b hb
  refine ⟨u, ?_⟩
  rw [principalUnitLogOfMixedChar_apply_toAdd, principalUnitLogSeriesOfWithZeroValuation]
  have harg : principalUnitSubOneOfWithZeroValuation v u =
      expSeriesFieldOfWithZeroValuation v x hnexp - 1 := by
    simp only [principalUnitSubOneOfWithZeroValuation, u,
      CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPowSubgroup_val,
      CompleteDVF.higherPrincipalUnitGroup.principalUnitOneAddOfMemPow_val,
      b]
    change (1 + (expSeriesFieldOfWithZeroValuation v x hnexp - 1)) - 1 =
      expSeriesFieldOfWithZeroValuation v x hnexp - 1
    exact add_sub_cancel_left 1 (expSeriesFieldOfWithZeroValuation v x hnexp - 1)
  rw [harg]
  exact logOnePlusSeries_expSeries_sub_one_eq_self_ofWithZeroValuation_scaled_of_threshold
    (p := p) v e x hnexp hvexp hnlog hvlog hthreshold hcomplete

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
