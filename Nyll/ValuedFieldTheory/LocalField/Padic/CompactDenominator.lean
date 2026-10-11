/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.Topology.Order.Compact

/-!
# A common denominator for a compact family of p-adic numbers

A continuous family on a compact space can be multiplied by one power of p
so that every value lies in the actual p-adic integer ring.
-/

namespace LocalFieldTheory

variable (p : ℕ) [Fact p.Prime]

/-- A compact continuous family of p-adic numbers has a uniform integral denominator. -/
theorem exists_pow_mul_norm_le_one {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    (f : Y → ℚ_[p]) (hf : Continuous f) :
    ∃ n : ℕ, ∀ y : Y, ‖(p : ℚ_[p]) ^ n * f y‖ ≤ 1 := by
  obtain ⟨b, hb⟩ := isCompact_univ.bddAbove_image (continuous_norm.comp hf).continuousOn
  let c : ℝ := max b 1
  have hc : 0 < c := lt_of_lt_of_le zero_lt_one (le_max_right b 1)
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p (one_div_pos.mpr hc)
  refine ⟨n, fun y => ?_⟩
  have hy : ‖f y‖ ≤ c := (hb ⟨y, Set.mem_univ y, rfl⟩).trans (le_max_left b 1)
  calc
    ‖(p : ℚ_[p]) ^ n * f y‖ = (p : ℝ) ^ (-(n : ℤ)) * ‖f y‖ := by
      rw [norm_mul, Padic.norm_p_pow]
    _ ≤ (p : ℝ) ^ (-(n : ℤ)) * c :=
      mul_le_mul_of_nonneg_left hy (zpow_nonneg (Nat.cast_nonneg p) _)
    _ ≤ 1 := (lt_div_iff₀ hc).mp hn |>.le

end LocalFieldTheory
