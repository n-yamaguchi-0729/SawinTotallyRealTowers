/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized

/-!
# Nondivisibility of a rank-one discrete value group

For each natural number greater than one, the image of a discrete valuation contains a
nonzero value that is not an nth power. A normalized valuation and uniformizer supply
the witness.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v

/-- A rank-one discrete value group is not divisible by any natural number
larger than one. The witness lies in the actual image of the valuation. -/
theorem exists_value_not_pow {K : Type u} [Field K] (D : DVF.{u, v} K)
    (n : ℕ) (hn : 1 < n) :
    ∃ x : K, x ≠ 0 ∧ ∀ y : K, D.valuation y ^ n ≠ D.valuation x := by
  obtain ⟨w, _hw, hring, π, hπ⟩ := D.exists_normalized_valuation_with_uniformizer
  have heq : w.IsEquiv D.valuation :=
    (_root_.Valuation.isEquiv_iff_valuationSubring _ _).mpr hring
  have hπne : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  refine ⟨π, hπne, ?_⟩
  intro y hy
  have hpow : w (y ^ n) = w π := heq.eq_iff.mpr (by rw [map_pow, hy])
  have hlog := congrArg WithZero.log hpow
  rw [map_pow, WithZero.log_pow, hπ, WithZero.log_exp, nsmul_eq_mul] at hlog
  have hdiv : (n : ℤ) ∣ -1 := ⟨WithZero.log (w y), hlog.symm⟩
  have hdivone : (n : ℤ) ∣ 1 := (dvd_neg).mp hdiv
  have hnat : n ∣ 1 := by exact_mod_cast hdivone
  exact (Nat.not_le_of_lt hn) (Nat.le_of_dvd (by decide : 0 < 1) hnat)

end ValuationTheory.DiscreteValuationField.DVF
