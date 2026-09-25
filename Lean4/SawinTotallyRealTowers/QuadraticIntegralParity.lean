/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.Multiplicity

set_option autoImplicit false

/-!
# Parity of integral quadratic coordinates

For a signed squarefree integer `d`, the norm numerator `a² - d b²`
is divisible by four precisely for even coordinates, or for odd coordinates
when `d` is one modulo four.
-/

namespace ClassFieldTower.Sawin

private theorem sq_mod_four_eq_zero_of_even {x : ℤ} (hx : Even x) :
    x ^ 2 % 4 = 0 := by
  have hpow : (2 : ℤ) ^ 2 ∣ x ^ 2 :=
    pow_dvd_pow_of_dvd (even_iff_two_dvd.mp hx) 2
  apply Int.dvd_iff_emod_eq_zero.mp
  simpa only [show (2 : ℤ) ^ 2 = 4 by decide] using hpow

/-- The parity criterion for half-integer coordinates in a quadratic field. -/
theorem four_dvd_sq_sub_mul_sq_iff
    (d a b : ℤ) (hd : Squarefree d.natAbs) :
    4 ∣ a ^ 2 - d * b ^ 2 ↔
      (Even a ∧ Even b) ∨ (Odd a ∧ Odd b ∧ d % 4 = 1) := by
  have hdFour : ¬ (4 : ℤ) ∣ d := by
    intro hFour
    have hUnit : IsUnit (2 : ℕ) :=
      hd 2 (Int.natAbs_dvd_natAbs.mpr hFour)
    exact (by decide : (2 : ℕ) ≠ 1) (Nat.isUnit_iff.mp hUnit)
  constructor
  · intro hDiv
    have hMod : (a ^ 2 - d * b ^ 2) % 4 = 0 :=
      Int.dvd_iff_emod_eq_zero.mp hDiv
    rcases Int.even_or_odd a with ha | ha
    · rcases Int.even_or_odd b with hb | hb
      · exact Or.inl ⟨ha, hb⟩
      · rw [Int.sub_emod, Int.mul_emod,
          sq_mod_four_eq_zero_of_even ha,
          Int.sq_emod_four_eq_one_of_odd hb, mul_one] at hMod
        have hdMod : d % 4 = 0 := by omega
        exact False.elim (hdFour (Int.dvd_iff_emod_eq_zero.mpr hdMod))
    · rcases Int.even_or_odd b with hb | hb
      · rw [Int.sub_emod, Int.mul_emod,
          Int.sq_emod_four_eq_one_of_odd ha,
          sq_mod_four_eq_zero_of_even hb, mul_zero] at hMod
        omega
      · rw [Int.sub_emod, Int.mul_emod,
          Int.sq_emod_four_eq_one_of_odd ha,
          Int.sq_emod_four_eq_one_of_odd hb, mul_one] at hMod
        exact Or.inr ⟨ha, hb, by omega⟩
  · intro hParity
    apply Int.dvd_iff_emod_eq_zero.mpr
    rcases hParity with ⟨ha, hb⟩ | ⟨ha, hb, hdMod⟩
    · simp only [Int.sub_emod, Int.mul_emod,
        sq_mod_four_eq_zero_of_even ha,
        sq_mod_four_eq_zero_of_even hb, mul_zero, Int.zero_emod, sub_zero]
    · simp only [Int.sub_emod, Int.mul_emod,
        Int.sq_emod_four_eq_one_of_odd ha,
        Int.sq_emod_four_eq_one_of_odd hb, hdMod, mul_one,
        show (1 : ℤ) % 4 = 1 by decide, sub_self, Int.zero_emod]

end ClassFieldTower.Sawin
