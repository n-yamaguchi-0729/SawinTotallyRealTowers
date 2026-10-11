/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex
import Mathlib.GroupTheory.ArchimedeanDensely

/-!
# Integral multiples by powers of the residue characteristic

The residue characteristic has value less than one. Its powers therefore
make any field element integral, by the Archimedean property of the
multiplicative integers with zero. Completeness is not needed.
-/

namespace Valuation

variable {K : Type*} [Field K]

/-- Every field element becomes integral after multiplication by a power
of the residue characteristic. -/
theorem exists_natCast_pow_mul_le_one
    (v : Valuation K (WithZero (Multiplicative ℤ))) (p : ℕ)
    [CharP (IsLocalRing.ResidueField v.valuationSubring) p] (b : K) :
    ∃ n : ℕ, v ((p : K) ^ n * b) ≤ 1 := by
  by_cases hb : b = 0
  · refine ⟨0, ?_⟩
    rw [hb, mul_zero, v.map_zero]
    exact zero_le_one
  · have hvb : v b ≠ 0 := v.ne_zero_iff.mpr hb
    obtain ⟨n, hn⟩ := exists_pow_lt₀ (v.natCast_residueChar_lt_one p)
      (Units.mk0 (v b) hvb)⁻¹
    have hbound : v (p : K) ^ n < (v b)⁻¹ := hn
    refine ⟨n, ?_⟩
    rw [v.map_mul, v.map_pow]
    calc
      v (p : K) ^ n * v b ≤ (v b)⁻¹ * v b :=
        mul_le_mul_of_nonneg_right hbound.le zero_le
      _ = 1 := inv_mul_cancel₀ hvb

end Valuation
