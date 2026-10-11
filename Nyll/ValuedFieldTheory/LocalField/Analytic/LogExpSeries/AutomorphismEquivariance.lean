/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationPreservingContinuous
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# The logarithm series commutes with valuation-preserving automorphisms

The actual valuation topology makes the field automorphism and its inverse
continuous. Consequently they commute with the total infinite sum defining
the logarithm; no supplied convergence or comparison theorem is needed.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A valuation-preserving automorphism commutes with the actual field log series. -/
theorem map_logOnePlusSeriesField_of_preserves
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (f : K ≃+* K) (hval : ∀ x : K, v (f x) = v x) (x : K) :
    f (logOnePlusSeriesFieldOfWithZeroValuation v x
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))) =
      logOnePlusSeriesFieldOfWithZeroValuation v (f x)
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hf : Continuous f :=
    ValuationTheory.DiscreteValuationField.Valuation.continuous_ringEquiv_of_preserves v f hval
  have hsym : ∀ y : K, v (f.symm y) = v y := by
    intro y
    have h := hval (f.symm y)
    rw [f.apply_symm_apply] at h
    exact h.symm
  have hfsym : Continuous f.symm :=
    ValuationTheory.DiscreteValuationField.Valuation.continuous_ringEquiv_of_preserves
      v f.symm hsym
  have hn : ∀ n : ℕ, ((n + 1 : ℕ) : K) ≠ 0 :=
    fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  change f (∑' n : ℕ, signedLogSeriesTermField x hn n) =
    ∑' n : ℕ, signedLogSeriesTermField (f x) hn n
  rw [Function.LeftInverse.map_tsum (g := f)
    (fun n : ℕ => signedLogSeriesTermField x hn n) hf hfsym f.symm_apply_apply]
  apply tsum_congr
  intro n
  simp only [signedLogSeriesTermField, logSeriesTermField, Units.val_mk0,
    _root_.map_mul, _root_.map_pow, _root_.map_neg, _root_.map_one,
    _root_.map_div₀, _root_.map_natCast]

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
