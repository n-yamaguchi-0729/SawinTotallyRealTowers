/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteNormCompleteExtension
import Mathlib.Data.Int.WithZero
import Nyll.ValuedFieldTheory.Valuation.PowerSubImage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Detecting automorphisms on power-minus-identity classes

The field-norm valuation restricts to the degree-th power of the base valuation.
After integer normalization, multiplying a nonzero extension-field element by a
suitable inverse uniformizer power makes its value exponent positive and not
divisible by the chosen exponent. It therefore cannot be a power minus itself.
Completeness is used for the norm valuation. No separability or residue-field
hypothesis is needed.
-/

namespace ValuationTheory.DiscreteValuationField

private theorem exists_nat_shift_pos_not_dvd
    (p d : ℕ) (hd : 0 < d) (hpd : ¬ p ∣ d) (m : ℤ) :
    ∃ n : ℕ, 0 < m + (n : ℤ) * d ∧ ¬ (p : ℤ) ∣ m + (n : ℤ) * d := by
  let n : ℕ := m.natAbs + 1
  have hn : (n : ℤ) = (m.natAbs : ℤ) + 1 := by
    simp only [n, Nat.cast_add, Nat.cast_one]
  have hm : -(m.natAbs : ℤ) ≤ m := by
    rw [← Int.abs_eq_natAbs]
    exact neg_abs_le m
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have hnpos : 0 < (n : ℤ) := by omega
  have hpos : 0 < m + (n : ℤ) * d := by nlinarith
  by_cases hdiv : (p : ℤ) ∣ m + (n : ℤ) * d
  · refine ⟨n + 1, ?_, ?_⟩
    · push_cast
      nlinarith
    · intro hdiv'
      have h : (p : ℤ) ∣ (d : ℤ) := by
        convert dvd_sub hdiv' hdiv using 1
        push_cast
        ring
      exact hpd (Int.natCast_dvd_natCast.mp h)
  · exact ⟨n, hpos, hdiv⟩

private theorem normalized_mul_not_pow_sub
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete v] (π : K) (hπ : v π = WithZero.exp (-1 : ℤ))
    (p : ℕ) (hp : 1 < p) (hpd : ¬ p ∣ Module.finrank K L) (a : L) (ha : a ≠ 0) :
    ∃ b : K, ∀ y : L, y ^ p - y ≠ algebraMap K L b * a := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : v.RankOne := _root_.Valuation.IsRankOneDiscrete.rankOne v (e := 2) (by norm_num)
  let : CompleteSpace K := ValuedExtension.completeSpace_of_completeDiscreteValuation v
  let w := ValuedExtension.finiteNormValuation (K := K) (L := L)
    (Γ := WithZero (Multiplicative ℤ))
  have ha0 : w a ≠ 0 := (map_ne_zero w).mpr ha
  obtain ⟨n, hnpos, hndiv⟩ := exists_nat_shift_pos_not_dvd p
    (Module.finrank K L) (Module.finrank_pos (R := K) (M := L)) hpd
      (WithZero.log (w a))
  let b : K := (π⁻¹) ^ n
  have hb : v b = WithZero.exp (n : ℤ) := by
    change v ((π⁻¹) ^ n) = _
    rw [map_pow, map_inv₀, hπ, ← WithZero.exp_neg]
    simp only [neg_neg, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_one]
  have hb0 : w (algebraMap K L b) ≠ 0 := by
    change ValuedExtension.finiteNormValuation (K := K) (L := L) (Γ := WithZero (Multiplicative ℤ))
      (algebraMap K L b) ≠ 0
    rw [ValuedExtension.finiteNormValuation_algebraMap]
    change v b ^ Module.finrank K L ≠ 0
    rw [hb]
    exact pow_ne_zero _ WithZero.exp_ne_zero
  have hlog : WithZero.log (w (algebraMap K L b * a)) =
      WithZero.log (w a) + (n : ℤ) * Module.finrank K L := by
    rw [map_mul, WithZero.log_mul hb0 ha0]
    change WithZero.log
      (ValuedExtension.finiteNormValuation (K := K) (L := L)
        (Γ := WithZero (Multiplicative ℤ)) (algebraMap K L b)) + _ = _
    rw [ValuedExtension.finiteNormValuation_algebraMap]
    change WithZero.log (v b ^ Module.finrank K L) + _ = _
    rw [hb, WithZero.log_pow, WithZero.log_exp]
    simp only [nsmul_eq_mul]
    ring
  refine ⟨b, w.pow_sub_ne_of_one_lt_of_log_not_dvd p hp _ ?_ ?_⟩
  · have hnonzero : w (algebraMap K L b * a) ≠ 0 := by
      rw [map_mul]
      exact mul_ne_zero hb0 ha0
    rw [← WithZero.exp_log hnonzero, WithZero.one_lt_exp_iff, hlog]
    exact hnpos
  · rw [hlog]
    exact hndiv

/-- A finite extension of degree not divisible by an exponent has a base multiple of every
nonzero element outside the image of the power-minus-identity map. -/
theorem CompleteDVF.exists_mul_not_pow_sub_of_not_dvd_finrank
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (base : CompleteDVF K) (p : ℕ) (hp : 1 < p)
    (hpd : ¬ p ∣ Module.finrank K L) (a : L) (ha : a ≠ 0) :
    ∃ b : K, ∀ y : L, y ^ p - y ≠ algebraMap K L b * a := by
  obtain ⟨v, hv, hring, π, hπ⟩ :=
    base.toDVF.exists_normalized_valuation_with_uniformizer
  let : v.IsRankOneDiscrete := hv
  have hc : Valuation.IsCompleteDiscrete v := by
    refine { isRankOneDiscrete := hv, isAdicComplete := ?_ }
    let P : ValuationSubring K → Prop := fun A =>
      IsAdicComplete (IsLocalRing.maximalIdeal A) A
    exact hring.symm ▸ (show P base.valuation.valuationSubring from
      Valuation.isAdicComplete base.valuation)
  exact normalized_mul_not_pow_sub v π hπ p hp hpd a ha

/-- Every nonidentity automorphism is detected on power-minus-identity classes
when the extension degree is not divisible by the exponent. -/
theorem CompleteDVF.exists_moved_pow_sub_class_of_not_dvd_finrank
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (base : CompleteDVF K) (p : ℕ) (hp : 1 < p)
    (hpd : ¬ p ∣ Module.finrank K L) (τ : L ≃ₐ[K] L) (hτ : τ ≠ 1) :
    ∃ x : L, ∀ y : L, y ^ p - y ≠ τ x - x := by
  obtain ⟨x, hx⟩ : ∃ x : L, τ x ≠ x := by
    by_contra h
    apply hτ
    ext x
    exact not_not.mp (fun hx => h ⟨x, hx⟩)
  obtain ⟨b, hb⟩ := base.exists_mul_not_pow_sub_of_not_dvd_finrank
    p hp hpd (τ x - x) (sub_ne_zero.mpr hx)
  refine ⟨algebraMap K L b * x, ?_⟩
  intro y
  simpa only [map_mul, τ.commutes, mul_sub] using hb y

end ValuationTheory.DiscreteValuationField
