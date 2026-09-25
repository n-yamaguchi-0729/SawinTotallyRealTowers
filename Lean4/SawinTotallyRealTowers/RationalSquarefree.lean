/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Cast.Defs

set_option autoImplicit false

/-!
# Signed squarefree representatives of rational square classes

Apply the natural-number squarefree decomposition to the product of the
absolute numerator and denominator. The numerator's sign then gives an
integer representative without introducing a square root in an extension.
-/

namespace ClassFieldTower.Sawin

/-- Every nonzero rational number is a nonzero square times a signed
squarefree integer. -/
theorem exists_squarefree_int_mul_sq (q : ℚ) (hq : q ≠ 0) :
    ∃ d : ℤ, ∃ r : ℚ,
      Squarefree d.natAbs ∧ d ≠ 0 ∧ r ≠ 0 ∧ q = (d : ℚ) * r ^ 2 := by
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.mpr hq
  have habs : 0 < q.num.natAbs := Int.natAbs_pos.mpr hnum
  obtain ⟨a, b, ha, hb, hab, haSquarefree⟩ :=
    Nat.sq_mul_squarefree_of_pos (Nat.mul_pos habs q.den_pos)
  let d : ℤ := q.num.sign * (a : ℤ)
  let r : ℚ := (b : ℚ) / (q.den : ℚ)
  have hdAbs : d.natAbs = a := by
    dsimp only [d]
    rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hnum,
      Int.natAbs_natCast, one_mul]
  have hd : d ≠ 0 := by
    intro hdZero
    have haZero : a = 0 := hdAbs.symm.trans (congrArg Int.natAbs hdZero)
    exact (Nat.ne_of_gt ha) haZero
  have hbRat : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hb)
  have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
  have hr : r ≠ 0 := div_ne_zero hbRat hden
  have habRat : (b : ℚ) ^ 2 * (a : ℚ) =
      (q.num.natAbs : ℚ) * (q.den : ℚ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun n : ℕ ↦ (n : ℚ)) hab
  have hsign : (q.num.sign : ℚ) * (q.num.natAbs : ℚ) = (q.num : ℚ) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using
      congrArg (fun n : ℤ ↦ (n : ℚ)) (Int.sign_mul_natAbs q.num)
  have hdNumerator : (d : ℚ) * (b : ℚ) ^ 2 =
      (q.num : ℚ) * (q.den : ℚ) := by
    calc
      (d : ℚ) * (b : ℚ) ^ 2 =
          (q.num.sign : ℚ) * ((a : ℚ) * (b : ℚ) ^ 2) := by
        simp only [d, Int.cast_mul, Int.cast_natCast, mul_assoc]
      _ = (q.num.sign : ℚ) * ((b : ℚ) ^ 2 * (a : ℚ)) :=
        congrArg (fun x : ℚ ↦ (q.num.sign : ℚ) * x)
          (mul_comm (a : ℚ) ((b : ℚ) ^ 2))
      _ = (q.num.sign : ℚ) *
          ((q.num.natAbs : ℚ) * (q.den : ℚ)) :=
        congrArg (fun x : ℚ ↦ (q.num.sign : ℚ) * x) habRat
      _ = (q.num : ℚ) * (q.den : ℚ) := by
        rw [← mul_assoc, hsign]
  have hqNumerator : q * (q.den : ℚ) = (q.num : ℚ) :=
    (eq_div_iff hden).mp q.num_div_den.symm
  refine ⟨d, r, ?_, hd, hr, ?_⟩
  · rw [hdAbs]
    exact haSquarefree
  · dsimp only [r]
    rw [div_pow, ← mul_div_assoc]
    apply (eq_div_iff (pow_ne_zero 2 hden)).mpr
    calc
      q * (q.den : ℚ) ^ 2 = (q * (q.den : ℚ)) * (q.den : ℚ) := by
        rw [pow_two, mul_assoc]
      _ = (q.num : ℚ) * (q.den : ℚ) :=
        congrArg (fun x : ℚ ↦ x * (q.den : ℚ)) hqNumerator
      _ = (d : ℚ) * (b : ℚ) ^ 2 := hdNumerator.symm

end ClassFieldTower.Sawin
