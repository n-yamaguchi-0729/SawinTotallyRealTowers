import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

/-!
# Integral elements expressed using a rational square root

A square root of an integer is integral. More generally, the element
`(m + n * α) / 2`, where `α ^ 2 = d`, is integral whenever
`4 ∣ m ^ 2 - d * n ^ 2`. The divisibility witness supplies the integer
constant coefficient of the monic polynomial `X ^ 2 - m * X + k`.
No degree or squarefreeness assumption is needed for this construction.
-/

open Polynomial

universe u

namespace ClassFieldTower.Sawin

/-- A square root of an integer in a ℚ-algebra is integral over ℤ. -/
theorem isIntegral_int_of_sq_eq_int
    (L : Type u) [Field L] [Algebra ℚ L] (d : ℤ) {α : L}
    (hα : α ^ 2 = algebraMap ℚ L (d : ℚ)) : IsIntegral ℤ α := by
  apply IsIntegral.of_pow (n := 2) (by decide)
  rw [hα]
  simpa only [map_intCast, algebraMap_int_eq, Int.coe_castRingHom] using
    (isIntegral_algebraMap (R := ℤ) (A := L) (x := d))

/-- The congruence `m ^ 2 ≡ d * n ^ 2 (mod 4)` makes the half-integer
linear combination of `1` and a square root of `d` integral over ℤ. -/
theorem isIntegral_half_int_linear_combination_of_four_dvd
    (L : Type u) [Field L] [Algebra ℚ L] (d m n : ℤ) {α : L}
    (hα : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hdiv : 4 ∣ m ^ 2 - d * n ^ 2) :
    IsIntegral ℤ
      ((algebraMap ℚ L (m : ℚ) + algebraMap ℚ L (n : ℚ) * α) / 2) := by
  let : CharZero L := Algebra.charZero_of_charZero ℚ L
  obtain ⟨k, hk⟩ := hdiv
  have hαL : α ^ 2 = (d : L) := by
    simpa only [map_intCast] using hα
  have hkL := congrArg (algebraMap ℤ L) hk
  simp only [map_sub, map_pow, map_mul, map_ofNat] at hkL
  refine ⟨X ^ 2 - (C m * X - C k), ?_, ?_⟩
  · apply monic_X_pow_sub
    apply lt_of_le_of_lt (degree_sub_le (C m * X) (C k))
    exact max_lt
      ((degree_C_mul_X_le m).trans_lt (by decide : (1 : WithBot ℕ) < 2))
      (degree_C_le.trans_lt (by decide : (0 : WithBot ℕ) < 2))
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, map_intCast]
    linear_combination (n : L) ^ 2 / 4 * hαL - (1 / 4 : L) * hkL

end ClassFieldTower.Sawin
