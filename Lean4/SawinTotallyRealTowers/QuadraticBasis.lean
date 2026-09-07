import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.SuccPred
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.RingTheory.PowerBasis

set_option autoImplicit false

/-!
# The basis associated to a quadratic generator

A generator of a quadratic extension of ℚ supplies the actual basis
`1, α`. Reindexing its power basis by `Fin 2` gives named basis vectors
and the rational coordinates of every element. No square relation is
needed for this linear-algebra construction.
-/

universe u

namespace ClassFieldTower.Sawin

/-- The basis `1, α` associated to a generator of a quadratic extension. -/
noncomputable def quadraticBasis
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (α : L) (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    Module.Basis (Fin 2) ℚ L :=
  let pb : PowerBasis ℚ L := PowerBasis.ofAdjoinEqTop
    (IsIntegral.of_finite ℚ α)
    ((IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
      (IsAlgebraic.of_finite ℚ α)).mp hGenerate)
  pb.basis.reindex
    (finCongr (pb.finrank.symm.trans
      (Algebra.IsQuadraticExtension.finrank_eq_two ℚ L)))

/-- Reindexing the quadratic power basis preserves its powers. -/
theorem quadraticBasis_apply
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (α : L) (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (i : Fin 2) : quadraticBasis L α hGenerate i = α ^ (i : ℕ) := by
  dsimp only [quadraticBasis]
  rw [Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    PowerBasis.ofAdjoinEqTop_gen, finCongr_symm_apply_coe]

/-- The first basis vector is one. -/
theorem quadraticBasis_apply_zero
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (α : L) (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    quadraticBasis L α hGenerate 0 = 1 := by
  rw [quadraticBasis_apply, Fin.val_zero, pow_zero]

/-- The second basis vector is the chosen generator. -/
theorem quadraticBasis_apply_one
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (α : L) (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤) :
    quadraticBasis L α hGenerate 1 = α := by
  rw [quadraticBasis_apply, Fin.val_one, pow_one]

/-- Every element has rational coordinates in the basis `1, α`. -/
theorem exists_rat_linear_combination_of_quadraticGenerator
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (α : L) (hGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (x : L) : ∃ a b : ℚ, x = algebraMap ℚ L a + algebraMap ℚ L b * α := by
  refine ⟨(quadraticBasis L α hGenerate).repr x 0,
    (quadraticBasis L α hGenerate).repr x 1, ?_⟩
  simpa only [Fin.sum_univ_two, quadraticBasis_apply_zero,
    quadraticBasis_apply_one, Algebra.smul_def, mul_one] using
    ((quadraticBasis L α hGenerate).sum_repr x).symm

end ClassFieldTower.Sawin
