import SawinTotallyRealTowers.QuadraticBasis
import SawinTotallyRealTowers.QuadraticTrace
import Mathlib.RingTheory.Discriminant

set_option autoImplicit false

/-!
# Discriminant of a quadratic square-root basis

The actual rational basis `1, α`, where `α² = d`, has diagonal trace
matrix with entries `2` and `2d`. Its discriminant is therefore `4d`.
No integrality or squarefreeness assumption is needed.
-/

universe u

namespace ClassFieldTower.Sawin

/-- The discriminant of the rational square-root basis is `4d`. -/
theorem discr_quadraticBasis
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (d : ℚ) (α : L) (hSquare : α ^ 2 = algebraMap ℚ L d)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    Algebra.discr ℚ (quadraticBasis L α hGenerate) = 4 * d := by
  have hTraceOne : Algebra.trace ℚ L (1 : L) = 2 := by
    simpa only [map_one, map_zero, zero_mul, add_zero, mul_one] using
      trace_quadratic_coordinates L d 1 0 α hSquare hGenerate
  have hTraceSquare : Algebra.trace ℚ L (α * α) = 2 * d := by
    rw [← pow_two, hSquare, Algebra.trace_algebraMap,
      Algebra.IsQuadraticExtension.finrank_eq_two ℚ L]
    simp only [two_smul, ← two_mul]
  rw [Algebra.discr_def, Matrix.det_fin_two]
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
    quadraticBasis_apply_zero, quadraticBasis_apply_one, one_mul, mul_one,
    hTraceOne, hTraceSquare, trace_quadratic_generator L d α hSquare hGenerate,
    mul_zero, sub_zero]
  ring

end ClassFieldTower.Sawin
