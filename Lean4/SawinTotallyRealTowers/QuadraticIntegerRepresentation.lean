import SawinTotallyRealTowers.QuadraticBasis
import SawinTotallyRealTowers.QuadraticIntegralCoordinates
import SawinTotallyRealTowers.QuadraticIntegralParity
import Mathlib.Algebra.Ring.Parity
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false

/-!
# Integer coordinates in a quadratic number field

The trace and norm conditions and their parity criterion give integer
coordinates for every algebraic integer. Away from `d = 1` modulo four
the generators are `1, α`. Every algebraic integer also has integer
coordinates in `1, (1 + α) / 2` for every squarefree `d`. When `d` is one
modulo four, the second generator is itself integral.
-/

open scoped NumberField

universe u

namespace ClassFieldTower.Sawin

private theorem exists_int_twice_coordinates
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (x : 𝓞 L) :
    ∃ m n : ℤ, (2 : L) * (x : L) = (m : L) + (n : L) * α ∧
      4 ∣ m ^ 2 - d * n ^ 2 := by
  obtain ⟨a, b, hCoordinates⟩ :=
    exists_rat_linear_combination_of_quadraticGenerator L α hGenerate (x : L)
  have hx : IsIntegral ℤ (algebraMap ℚ L a + algebraMap ℚ L b * α) := by
    rw [← hCoordinates]
    exact x.isIntegral_coe
  obtain ⟨m, n, hm, hn, hDiv⟩ :=
    exists_int_quadratic_coordinates_of_isIntegral L d hd a b α hSquare hGenerate hx
  have hmL : (2 : L) * algebraMap ℚ L a = (m : L) := by
    simpa only [map_mul, map_ofNat, map_intCast] using congrArg (algebraMap ℚ L) hm
  have hnL : (2 : L) * algebraMap ℚ L b = (n : L) := by
    simpa only [map_mul, map_ofNat, map_intCast] using congrArg (algebraMap ℚ L) hn
  refine ⟨m, n, ?_, hDiv⟩
  rw [hCoordinates, mul_add, ← mul_assoc, hmL, hnL]

/-- When the squarefree radicand is not one modulo four, every algebraic
integer has integer coordinates in `1, α`. -/
theorem exists_int_linear_combination_of_mod_four_ne_one
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hMod : d % 4 ≠ 1) (x : 𝓞 L) :
    ∃ m n : ℤ, (x : L) = (m : L) + (n : L) * α := by
  obtain ⟨m, n, hCoordinates, hDiv⟩ :=
    exists_int_twice_coordinates L d hd α hSquare hGenerate x
  have hEven : Even m ∧ Even n :=
    ((four_dvd_sq_sub_mul_sq_iff d m n hd).mp hDiv).resolve_right
      (fun hOdd ↦ hMod hOdd.2.2)
  obtain ⟨a, ha⟩ := even_iff_two_dvd.mp hEven.1
  obtain ⟨b, hb⟩ := even_iff_two_dvd.mp hEven.2
  refine ⟨a, b, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (2 : L) ≠ 0)
  calc
    (2 : L) * (x : L) = (m : L) + (n : L) * α := hCoordinates
    _ = 2 * ((a : L) + (b : L) * α) := by
      simp only [ha, hb, Int.cast_mul, Int.cast_ofNat]
      ring

/-- Every algebraic integer has integer coordinates in `1, (1 + α) / 2`.
The parity of the two half-integer coordinates is the same, so this
representation does not require a congruence assumption on `d`. -/
theorem exists_int_linear_combination_of_half_quadraticGenerator
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (x : 𝓞 L) :
    ∃ m n : ℤ, (x : L) = (m : L) + (n : L) * ((1 + α) / 2) := by
  obtain ⟨m, n, hCoordinates, hDiv⟩ :=
    exists_int_twice_coordinates L d hd α hSquare hGenerate x
  have hEven : Even (m - n) := by
    rcases (four_dvd_sq_sub_mul_sq_iff d m n hd).mp hDiv with hEven | hOdd
    · exact hEven.1.sub hEven.2
    · exact hOdd.1.sub_odd hOdd.2.1
  obtain ⟨a, ha⟩ := even_iff_two_dvd.mp hEven
  have haL : (m : L) - (n : L) = 2 * (a : L) := by
    simpa only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat] using
      congrArg (fun z : ℤ ↦ (z : L)) ha
  refine ⟨a, n, ?_⟩
  apply mul_left_cancel₀ (by norm_num : (2 : L) ≠ 0)
  calc
    (2 : L) * (x : L) = (m : L) + (n : L) * α := hCoordinates
    _ = 2 * ((a : L) + (n : L) * ((1 + α) / 2)) := by
      linear_combination haL

end ClassFieldTower.Sawin
