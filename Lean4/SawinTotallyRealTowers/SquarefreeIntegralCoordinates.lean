import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Rat.Cast.Defs

set_option autoImplicit false

/-!
# Integral rational coordinates after multiplication by a squarefree integer

If a signed squarefree integer times the square of a rational number is
integral, the denominator squared divides the squarefree integer. Coprimality
of the rational numerator and denominator then forces the denominator to be one.
-/

namespace ClassFieldTower.Sawin

/-- A rational number whose square becomes integral after multiplication
by a signed squarefree integer is itself integral. -/
theorem exists_int_eq_of_squarefree_mul_sq_eq_int
    (d : ℤ) (hd : Squarefree d.natAbs) (x : ℚ)
    (hx : ∃ m : ℤ, (d : ℚ) * x ^ 2 = (m : ℚ)) :
    ∃ n : ℤ, x = (n : ℚ) := by
  obtain ⟨m, hm⟩ := hx
  have hden : (x.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr x.den_ne_zero
  have hRat : (d : ℚ) * (x.num : ℚ) ^ 2 =
      (m : ℚ) * (x.den : ℚ) ^ 2 := by
    apply (div_eq_iff (pow_ne_zero 2 hden)).mp
    rw [mul_div_assoc, ← div_pow, x.num_div_den]
    exact hm
  have hInt : d * x.num ^ 2 = m * (x.den : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using hRat
  have hNat : d.natAbs * x.num.natAbs ^ 2 = m.natAbs * x.den ^ 2 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] using
      congrArg Int.natAbs hInt
  have hdenDvdProduct : x.den ^ 2 ∣ d.natAbs * x.num.natAbs ^ 2 :=
    ⟨m.natAbs, hNat.trans (Nat.mul_comm m.natAbs (x.den ^ 2))⟩
  have hCoprime : (x.den ^ 2).Coprime (x.num.natAbs ^ 2) :=
    Nat.Coprime.pow 2 2 x.reduced.symm
  have hdenDvd : x.den ^ 2 ∣ d.natAbs :=
    hCoprime.dvd_of_dvd_mul_right hdenDvdProduct
  have hdenUnit : IsUnit x.den := by
    apply hd x.den
    simpa only [pow_two] using hdenDvd
  have hdenOne : x.den = 1 := Nat.isUnit_iff.mp hdenUnit
  exact ⟨x.num, (Rat.coe_int_num_of_den_eq_one hdenOne).symm⟩

end ClassFieldTower.Sawin
