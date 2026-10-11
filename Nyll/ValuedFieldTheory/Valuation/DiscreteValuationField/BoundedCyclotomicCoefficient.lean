/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.BoundedCyclotomicExponent
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.IntCastValuation
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex

/-!
# Strict growth from a bounded cyclotomic coefficient

In mixed characteristic, a bounded exponent different from one gives a
coefficient `(1-a)/p^(s+1)` of value strictly greater than one. The numerator
has smaller p-adic order than the denominator. No completeness, discreteness,
or finite residue-field hypothesis is used.
-/

namespace Valuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- A nontrivial bounded cyclotomic exponent gives a coefficient whose
multiplicative value is strictly greater than one. -/
theorem one_lt_boundedCyclotomicCoefficient
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p a s : ℕ)
    [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (ha : a < p ^ (s + 1)) (ha1 : a ≠ 1) :
    1 < v ((1 - (a : K)) / (p : K) ^ (s + 1)) := by
  obtain ⟨hz, ht⟩ :=
    ValuationTheory.one_sub_natCast_ne_zero_and_padicValInt_lt p a s ha ha1
  have hp : 0 < v (p : K) :=
    (v.pos_iff).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hnum : v (1 - (a : K)) = v (p : K) ^ padicValInt p (1 - (a : ℤ)) := by
    simpa only [Int.cast_sub, Int.cast_one, Int.cast_natCast] using
      v.intCast_eq_pow_padicValInt p (1 - (a : ℤ)) hz
  rw [v.map_div, v.map_pow, hnum]
  exact (one_lt_div₀ (pow_pos hp (s + 1))).mpr
    (pow_lt_pow_right_of_lt_one₀ hp (v.natCast_residueChar_lt_one p) ht)

end Valuation
