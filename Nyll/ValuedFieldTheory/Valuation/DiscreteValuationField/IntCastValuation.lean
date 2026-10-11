/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NatCastValuation

/-!
# Values of integers in a valued field

The value of a nonzero integer is determined by its p-adic order at the
residue characteristic. Taking its natural absolute value reduces the formula
to the natural-number case, without a characteristic-zero hypothesis.
-/

namespace Valuation

universe u w

variable {K : Type u} [Field K]
variable {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]

/-- The value of a nonzero integer is the residue prime's value raised
to the integer's p-adic order. -/
theorem intCast_eq_pow_padicValInt (v : Valuation K Γ₀)
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (z : ℤ) (hz : z ≠ 0) :
    v (z : K) = v (p : K) ^ padicValInt p z := by
  have hsign : v (z : K) = v (z.natAbs : K) := by
    rcases Int.natAbs_eq z with h | h
    · simpa only [Int.cast_natCast] using congrArg (fun t : ℤ => v (t : K)) h
    · simpa only [Int.cast_neg, Int.cast_natCast, v.map_neg] using
        congrArg (fun t : ℤ => v (t : K)) h
  exact hsign.trans (v.natCast_eq_pow_padicValNat p z.natAbs
    (Int.natAbs_ne_zero.mpr hz))

end Valuation
