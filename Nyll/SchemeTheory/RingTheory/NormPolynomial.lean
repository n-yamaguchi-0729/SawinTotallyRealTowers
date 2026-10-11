/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The polynomial defining a field norm in basis coordinates

The determinant of the actual multiplication matrix gives a homogeneous polynomial
of degree equal to the extension dimension. Its evaluation is the actual algebra norm.
This construction is shared input for norm equations and the cohomology of function fields.
-/

noncomputable section

open scoped BigOperators

namespace Module.Basis

variable {F E ι : Type*} [Field F] [Field E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]

/-- The actual norm as a polynomial in the coordinates of a basis. -/
def normPolynomial (b : Basis ι F E) : MvPolynomial ι F :=
  Matrix.det (Matrix.of fun i j =>
    ∑ k, MvPolynomial.C (b.repr (b k * b j) i) * MvPolynomial.X k)

theorem eval_normPolynomial (b : Basis ι F E) (x : ι → F) :
    MvPolynomial.eval x b.normPolynomial = Algebra.norm F (∑ i, x i • b i) := by
  rw [normPolynomial, RingHom.map_det, Algebra.norm_eq_matrix_det b]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    MvPolynomial.eval_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Algebra.leftMulMatrix_eq_repr_mul, Finset.sum_mul, smul_mul_assoc, map_sum,
    map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k hk
  exact mul_comm _ _

theorem normPolynomial_isHomogeneous (b : Basis ι F E) :
    b.normPolynomial.IsHomogeneous (Fintype.card ι) := by
  classical
  rw [normPolynomial, Matrix.det_apply']
  simp only [Matrix.of_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro s hs
  have hprod :
      (∏ i, ∑ k, MvPolynomial.C (b.repr (b k * b i) (s i)) *
        MvPolynomial.X k).IsHomogeneous (Fintype.card ι) := by
    have h := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i => ∑ k, MvPolynomial.C (b.repr (b k * b i) (s i)) * MvPolynomial.X k)
      (fun _ => 1) (fun i _ =>
        MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
          (fun k _ => MvPolynomial.isHomogeneous_C_mul_X _ _))
    simpa only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using h
  simpa only [map_intCast] using
    hprod.C_mul ((Equiv.Perm.sign s : ℤ) : F)

end Module.Basis
