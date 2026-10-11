/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.Algebra.CharP.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Valuation.Integers

/-!
# Values of natural numbers in a valued field

The part of a natural number prime to the residue characteristic has nonzero
residue and is therefore a unit of the valuation ring. Thus its value is one,
and the value of the natural number is determined by its prime-power factor.
No discreteness, completeness, residue-field finiteness, or characteristic-zero
hypothesis is needed. The existing discrete-valuation-field API is retained.
-/

namespace Valuation

universe u v

variable {K : Type u} [Field K]
variable {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]

/-- The value of a nonzero natural number is the value of its
residue-characteristic prime-power factor. -/
theorem natCast_eq_pow_padicValNat (v : Valuation K Γ₀)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (n : ℕ) (hn : n ≠ 0) :
    v (n : K) = v (p : K) ^ padicValNat p n := by
  let k : ℕ := padicValNat p n
  let a : ℕ := n / p ^ k
  have hfactor : p ^ k * a = n := Nat.mul_div_cancel' pow_padicValNat_dvd
  have ha : ¬ p ∣ a := by
    intro hpa
    apply pow_succ_padicValNat_not_dvd (p := p) hn
    obtain ⟨b, hb⟩ := hpa
    refine ⟨b, ?_⟩
    calc
      n = p ^ k * a := hfactor.symm
      _ = p ^ k * (p * b) := by rw [hb]
      _ = p ^ (k + 1) * b := by rw [pow_succ, mul_assoc]
  have haunit : IsUnit (a : v.valuationSubring) := by
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (a : v.valuationSubring)).mp
    rw [map_natCast]
    exact (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField v.valuationSubring) p a).not.mpr ha
  have haval : v (a : K) = 1 := by
    have h := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.valuationSubring.integers (v := v))).mp haunit
    simpa only [map_natCast] using h
  have hcast : (n : K) = (p : K) ^ k * (a : K) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun m : ℕ => (m : K)) hfactor.symm
  rw [hcast, v.map_mul, v.map_pow, haval, mul_one]

end Valuation

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v

variable {K : Type u} [Field K]

/-- The natural-number valuation formula for a chosen discrete valuation field. -/
theorem valuation_natCast_eq_pow_padicValNat (F : DVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP F.residueField p]
    (n : ℕ) (hn : n ≠ 0) :
    F.valuation (n : K) = F.valuation (p : K) ^ padicValNat p n :=
  F.valuation.natCast_eq_pow_padicValNat p n hn

end ValuationTheory.DiscreteValuationField.DVF
