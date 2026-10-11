/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic

/-!
# The p-adic order of a bounded cyclotomic exponent

If a natural exponent below `p^(s+1)` differs from one, its difference from
one is nonzero and has p-adic order below `s+1`. The absolute value of that
integer is strictly below the modulus, so divisibility by the modulus is
impossible. The exponent zero and the prime two are included.
-/

namespace ValuationTheory

/-- A bounded exponent different from one has nonzero difference from one
and p-adic order strictly below the selected prime-power level. -/
theorem one_sub_natCast_ne_zero_and_padicValInt_lt
    (p a s : ℕ) [Fact p.Prime]
    (ha : a < p ^ (s + 1)) (ha1 : a ≠ 1) :
    1 - (a : ℤ) ≠ 0 ∧ padicValInt p (1 - (a : ℤ)) < s + 1 := by
  have hne : 1 - (a : ℤ) ≠ 0 := by omega
  have hmodulus : 1 < p ^ (s + 1) :=
    one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero s)
  have habs : (1 - (a : ℤ)).natAbs < p ^ (s + 1) := by
    rcases Int.natAbs_eq (1 - (a : ℤ)) with h | h <;> omega
  refine ⟨hne, ?_⟩
  by_contra hnot
  have hle : s + 1 ≤ padicValInt p (1 - (a : ℤ)) := not_lt.mp hnot
  have hdiv : (p : ℤ) ^ (s + 1) ∣ 1 - (a : ℤ) :=
    (padicValInt_dvd_iff (p := p) (s + 1) (1 - (a : ℤ))).mpr (Or.inr hle)
  have habs' : (1 - (a : ℤ)).natAbs < ((p : ℤ) ^ (s + 1)).natAbs := by
    simpa only [Int.natAbs_pow, Int.natAbs_natCast] using habs
  exact hne (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv habs')

end ValuationTheory
