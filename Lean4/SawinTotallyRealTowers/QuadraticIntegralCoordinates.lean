import SawinTotallyRealTowers.QuadraticTrace
import SawinTotallyRealTowers.SquarefreeIntegralCoordinates
import SawinTotallyRealTowers.QuadraticIntegralGenerator
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.RingTheory.Norm.Transitivity

set_option autoImplicit false

/-!
# Integral coordinates in a quadratic number field

The trace and norm of an algebraic integer are integral. For a square-root
generator of signed squarefree square `d`, these identities force both
coordinates to be half-integers and give the congruence modulo four.
Conversely, the congruence supplies a monic integer polynomial.
-/

universe u

namespace ClassFieldTower.Sawin

/-- An integral element in squarefree quadratic coordinates has half-integer
coordinates satisfying the norm congruence modulo four. -/
theorem exists_int_quadratic_coordinates_of_isIntegral
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (a b : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hx : IsIntegral ℤ (algebraMap ℚ L a + algebraMap ℚ L b * α)) :
    ∃ m n : ℤ, 2 * a = (m : ℚ) ∧ 2 * b = (n : ℚ) ∧ 4 ∣ m ^ 2 - d * n ^ 2 := by
  have hTrace : IsIntegral ℤ (2 * a) := by
    simpa only [trace_quadratic_coordinates L (d : ℚ) a b α hSquare hGenerate] using
      (Algebra.isIntegral_trace (L := ℚ) hx)
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hTrace
  change (m : ℚ) = 2 * a at hm
  have hNorm : IsIntegral ℤ (a ^ 2 - (d : ℚ) * b ^ 2) := by
    simpa only [norm_quadratic_coordinates L (d : ℚ) a b α hSquare hGenerate] using
      (Algebra.isIntegral_norm ℚ hx)
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hNorm
  change (k : ℚ) = a ^ 2 - (d : ℚ) * b ^ 2 at hk
  have hTwiceSquare : (d : ℚ) * (2 * b) ^ 2 = ((m ^ 2 - 4 * k : ℤ) : ℚ) := by
    push_cast
    rw [hm, hk]
    ring
  obtain ⟨n, hn⟩ := exists_int_eq_of_squarefree_mul_sq_eq_int d hd (2 * b)
    ⟨m ^ 2 - 4 * k, hTwiceSquare⟩
  refine ⟨m, n, hm.symm, hn, k, ?_⟩
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [hm, ← hn, hk]
  ring

/-- Integrality in squarefree quadratic coordinates is equivalent to
half-integer coordinates satisfying the norm congruence modulo four. -/
theorem isIntegral_quadratic_coordinates_iff
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (a b : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    IsIntegral ℤ (algebraMap ℚ L a + algebraMap ℚ L b * α) ↔
      ∃ m n : ℤ, 2 * a = (m : ℚ) ∧ 2 * b = (n : ℚ) ∧ 4 ∣ m ^ 2 - d * n ^ 2 := by
  constructor
  · exact exists_int_quadratic_coordinates_of_isIntegral L d hd a b α hSquare hGenerate
  · rintro ⟨m, n, hm, hn, hDiv⟩
    let : CharZero L := Algebra.charZero_of_charZero ℚ L
    have hmL : (2 : L) * algebraMap ℚ L a = algebraMap ℚ L (m : ℚ) := by
      simpa only [map_mul, map_ofNat] using congrArg (algebraMap ℚ L) hm
    have hnL : (2 : L) * algebraMap ℚ L b = algebraMap ℚ L (n : ℚ) := by
      simpa only [map_mul, map_ofNat] using congrArg (algebraMap ℚ L) hn
    have hCoordinates : algebraMap ℚ L a + algebraMap ℚ L b * α =
        (algebraMap ℚ L (m : ℚ) + algebraMap ℚ L (n : ℚ) * α) / 2 := by
      apply (eq_div_iff (by norm_num : (2 : L) ≠ 0)).mpr
      linear_combination hmL + hnL * α
    rw [hCoordinates]
    exact isIntegral_half_int_linear_combination_of_four_dvd L d m n hSquare hDiv

end ClassFieldTower.Sawin
