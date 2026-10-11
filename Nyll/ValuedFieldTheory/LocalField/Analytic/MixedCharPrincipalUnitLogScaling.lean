/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.PrimePowerIntegralMultiple
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogImage

/-!
# Prime-power multiples in the principal-unit logarithm image

First multiply an arbitrary field element by a power of the residue prime
to make it integral. The existing exponential construction then realizes
an additional factor of `p²` as the logarithm of an actual principal unit.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {K : Type*} [Field K] [CharZero K]

/-- Every field element has a prime-power multiple in the principal-unit
logarithm image. -/
theorem exists_principalUnit_log_eq_natCast_pow_mul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (b : K) :
    ∃ (n : ℕ) (u : CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1),
      (principalUnitLogOfMixedChar v p u).toAdd = (p : K) ^ n * b := by
  obtain ⟨n, hn⟩ := v.exists_natCast_pow_mul_le_one p b
  obtain ⟨u, hu⟩ := exists_principalUnit_log_eq_natCast_sq_mul v p
    ⟨(p : K) ^ n * b, hn⟩
  refine ⟨n + 2, u, ?_⟩
  change (principalUnitLogOfMixedChar v p u).toAdd =
    (p : K) ^ 2 * ((p : K) ^ n * b) at hu
  rw [← mul_assoc, ← pow_add, Nat.add_comm 2 n] at hu
  exact hu

/-- A nonzero field element has a nonzero prime-power multiple in the
principal-unit logarithm image. -/
theorem exists_principalUnit_log_eq_natCast_pow_mul_ne_zero
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (b : K) (hb : b ≠ 0) :
    ∃ (n : ℕ) (u : CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1),
      (principalUnitLogOfMixedChar v p u).toAdd = (p : K) ^ n * b ∧
      (principalUnitLogOfMixedChar v p u).toAdd ≠ 0 := by
  obtain ⟨n, u, hu⟩ := exists_principalUnit_log_eq_natCast_pow_mul v p b
  refine ⟨n, u, hu, ?_⟩
  rw [hu]
  exact mul_ne_zero (pow_ne_zero n
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)) hb

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
