import SawinTotallyRealTowers.QuadraticGenerator
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Trace.Basic

set_option autoImplicit false

/-!
# Traces and norms in quadratic coordinates

A square-root generator of a quadratic extension has minimal polynomial
`X² - d`. Its trace and norm, and those of every rational linear combination
of `1` and the generator, follow from the power basis and a two-dimensional
determinant identity.
-/

noncomputable section

universe u

namespace ClassFieldTower.Sawin

variable (L : Type u) [Field L] [Algebra ℚ L]
    [Algebra.IsQuadraticExtension ℚ L]

/-- The square-root generator of a quadratic extension has the expected
minimal polynomial. -/
theorem minpoly_quadratic_generator (d : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L d)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    minpoly ℚ α = Polynomial.X ^ 2 - Polynomial.C d := by
  have hPower : α ^ Module.finrank ℚ L = algebraMap ℚ L d := by
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two ℚ L] using hSquare
  have hIrred : Irreducible (Polynomial.X ^ 2 - Polynomial.C d) := by
    simpa only [Algebra.IsQuadraticExtension.finrank_eq_two ℚ L] using
      irreducible_X_pow_sub_C_of_root_adjoin_eq_top hPower hGenerate
  symm
  apply minpoly.eq_of_irreducible_of_monic hIrred
  · simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hSquare,
      sub_self]
  · exact Polynomial.monic_X_pow_sub_C d (by decide : (2 : ℕ) ≠ 0)

/-- A square-root generator has trace zero. -/
theorem trace_quadratic_generator (d : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L d)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    Algebra.trace ℚ L α = 0 := by
  have hAdjoin : Algebra.adjoin ℚ ({α} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hGenerate,
      IntermediateField.top_toSubalgebra]
  let pb : PowerBasis ℚ L := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ α) hAdjoin
  simpa only [pb, PowerBasis.ofAdjoinEqTop_gen,
    minpoly_quadratic_generator L d α hSquare hGenerate, Polynomial.nextCoeff,
    Polynomial.natDegree_X_pow_sub_C, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C, Nat.reduceSub, Nat.reduceEqDiff, ↓reduceIte, sub_self, neg_zero]
    using PowerBasis.trace_gen_eq_nextCoeff_minpoly pb

/-- A square-root generator of square `d` has norm `-d`. -/
theorem norm_quadratic_generator (d : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L d)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    Algebra.norm ℚ α = -d := by
  have hAdjoin : Algebra.adjoin ℚ ({α} : Set L) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hGenerate,
      IntermediateField.top_toSubalgebra]
  let pb : PowerBasis ℚ L := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ α) hAdjoin
  simpa only [pb, PowerBasis.ofAdjoinEqTop_gen, PowerBasis.ofAdjoinEqTop_dim,
    minpoly_quadratic_generator L d α hSquare hGenerate,
    Polynomial.natDegree_X_pow_sub_C, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_zero, Nat.reduceEqDiff, ↓reduceIte, even_two, Even.neg_pow,
    one_pow, one_mul, zero_sub]
    using Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb

/-- The trace is twice the constant coordinate. -/
theorem trace_quadratic_coordinates (d a b : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L d)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    Algebra.trace ℚ L (algebraMap ℚ L a + algebraMap ℚ L b * α) = 2 * a := by
  rw [map_add, ← Algebra.smul_def, map_smul, trace_quadratic_generator L d α hSquare hGenerate,
    smul_zero, add_zero, Algebra.trace_algebraMap,
    Algebra.IsQuadraticExtension.finrank_eq_two ℚ L]
  simp only [two_smul]
  ring

private theorem norm_quadratic_affine (a b : ℚ) (α : L) :
    Algebra.norm ℚ (algebraMap ℚ L a + algebraMap ℚ L b * α) =
      a ^ 2 + a * b * Algebra.trace ℚ L α + b ^ 2 * Algebra.norm ℚ α := by
  let basis : Module.Basis (Fin 2) ℚ L := (Module.finBasis ℚ L).reindex
    (finCongr (Algebra.IsQuadraticExtension.finrank_eq_two ℚ L))
  rw [Algebra.norm_eq_matrix_det basis, Algebra.trace_eq_matrix_trace basis,
    Algebra.norm_eq_matrix_det basis]
  have hCoordinates : algebraMap ℚ L a + algebraMap ℚ L b * α = a • (1 : L) + b • α := by
    simp only [Algebra.smul_def, mul_one]
  rw [hCoordinates, map_add, map_smul, map_smul, map_one]
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  norm_num
  ring

/-- The norm is the binary quadratic form `a² - d b²`. -/
theorem norm_quadratic_coordinates (d a b : ℚ) (α : L)
    (hSquare : α ^ 2 = algebraMap ℚ L d)
    (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    Algebra.norm ℚ (algebraMap ℚ L a + algebraMap ℚ L b * α) = a ^ 2 - d * b ^ 2 := by
  rw [norm_quadratic_affine, trace_quadratic_generator L d α hSquare hGenerate,
    norm_quadratic_generator L d α hSquare hGenerate]
  ring

end ClassFieldTower.Sawin
