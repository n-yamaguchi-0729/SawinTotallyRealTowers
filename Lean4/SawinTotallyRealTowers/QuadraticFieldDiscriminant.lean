import SawinTotallyRealTowers.QuadraticBasisDiscriminant
import SawinTotallyRealTowers.QuadraticIntegerBasis
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Discriminants of squarefree quadratic number fields

The constructed bases of the full ring of integers determine the number
field discriminant. Integer traces agree with rational traces after scalar
extension, so the two-by-two trace determinants give `4d` or `d` according
to the signed radicand modulo four.
-/

open scoped NumberField
open NumberField

universe u

namespace ClassFieldTower.Sawin

private theorem coe_discr_int_fin_two
    (L : Type u) [Field L] [NumberField L] (b : Fin 2 → 𝓞 L) :
    (Algebra.discr ℤ b : ℚ) = Algebra.discr ℚ (fun i ↦ (b i : L)) := by
  simp only [Algebra.discr_def, Matrix.det_fin_two, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, Int.cast_sub, Int.cast_mul, Algebra.coe_trace_int,
    RingOfIntegers.coe_eq_algebraMap, map_mul]

/-- A signed squarefree radicand not congruent to one modulo four gives
number field discriminant `4d`. -/
theorem numberField_discr_of_mod_four_ne_one
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hMod : d % 4 ≠ 1) : NumberField.discr L = 4 * d := by
  let B : Module.Basis (Fin 2) ℤ (𝓞 L) :=
    quadraticIntegerBasisOfModFourNeOne L d hd α hSquare hGenerate hMod
  have hBasis : (fun i : Fin 2 ↦ (B i : L)) = quadraticBasis L α hGenerate := by
    funext i
    fin_cases i
    · change (B 0 : L) = quadraticBasis L α hGenerate 0
      simp only [B, quadraticIntegerBasisOfModFourNeOne_apply_zero,
        map_one, quadraticBasis_apply_zero]
    · change (B 1 : L) = quadraticBasis L α hGenerate 1
      simp only [B, quadraticIntegerBasisOfModFourNeOne_apply_one,
        coe_quadraticIntegerGenerator, quadraticBasis_apply_one]
  rw [← NumberField.discr_eq_discr L B]
  apply Int.cast_injective (α := ℚ)
  rw [coe_discr_int_fin_two L, hBasis, discr_quadraticBasis L (d : ℚ) α hSquare hGenerate]
  simp only [Int.cast_mul, Int.cast_ofNat]

/-- A signed squarefree radicand congruent to one modulo four gives
number field discriminant `d`. -/
theorem numberField_discr_of_mod_four_eq_one
    (L : Type u) [Field L] [NumberField L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℤ) (hd : Squarefree d.natAbs) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hMod : d % 4 = 1) : NumberField.discr L = d := by
  let B : Module.Basis (Fin 2) ℤ (𝓞 L) :=
    quadraticIntegerBasisOfModFourEqOne L d hd α hSquare hGenerate hMod
  have hBZero : (B 0 : L) = 1 := by
    simp only [B, quadraticIntegerBasisOfModFourEqOne_apply_zero, map_one]
  have hBOne : (B 1 : L) = (1 + α) / 2 := by
    simp only [B, quadraticIntegerBasisOfModFourEqOne_apply_one,
      coe_quadraticHalfIntegerGenerator]
  have hTraceOne : Algebra.trace ℚ L (1 : L) = 2 := by
    simpa only [map_one, map_zero, zero_mul, add_zero, mul_one] using
      trace_quadratic_coordinates L (d : ℚ) 1 0 α hSquare hGenerate
  have hHalf : (1 + α) / 2 =
      algebraMap ℚ L (1 / 2 : ℚ) + algebraMap ℚ L (1 / 2 : ℚ) * α := by
    simp only [map_div₀, map_one, map_ofNat]
    ring
  have hTraceHalf : Algebra.trace ℚ L ((1 + α) / 2) = 1 := by
    rw [hHalf, trace_quadratic_coordinates L (d : ℚ) (1 / 2) (1 / 2) α hSquare hGenerate]
    norm_num
  have hHalfSquare : ((1 + α) / 2) * ((1 + α) / 2) =
      algebraMap ℚ L ((1 + (d : ℚ)) / 4) + algebraMap ℚ L (1 / 2 : ℚ) * α := by
    simp only [map_div₀, map_add, map_one, map_ofNat]
    linear_combination (1 / 4 : L) * hSquare
  have hTraceHalfSquare : Algebra.trace ℚ L (((1 + α) / 2) * ((1 + α) / 2)) =
      (1 + (d : ℚ)) / 2 := by
    rw [hHalfSquare,
      trace_quadratic_coordinates L (d : ℚ) ((1 + (d : ℚ)) / 4) (1 / 2) α hSquare hGenerate]
    ring
  rw [← NumberField.discr_eq_discr L B]
  apply Int.cast_injective (α := ℚ)
  rw [coe_discr_int_fin_two L, Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    hBZero, hBOne, one_mul, mul_one,
    hTraceOne, hTraceHalf, hTraceHalfSquare]
  ring

end ClassFieldTower.Sawin
