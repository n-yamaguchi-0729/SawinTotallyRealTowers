/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.CoordinateRing
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# Partial derivatives on affine plane curves

This file develops the first-order polynomial decomposition used in
Fried--Jarden, Lemma 6.2.3.  Besides writing a polynomial minus its value at a
point as a combination of the two translated coordinates, the construction
controls the values of both coefficients: they are the two partial
derivatives at the point.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace AffinePlaneCurve

open MvPolynomial

universe u

variable {K : Type u} [Field K]

/-- The value at `p` of the `i`-th formal partial derivative of `f`. -/
def partialAt
    {f : BivariatePolynomial K} (p : RationalPoint f) (i : Fin 2) : K :=
  polynomialEval p (MvPolynomial.pderiv i f)

/-- A rational point is simple when some partial derivative is nonzero. -/
def IsSimple
    {f : BivariatePolynomial K} (p : RationalPoint f) : Prop :=
  ∃ i : Fin 2, partialAt p i ≠ 0

/--
First-order decomposition at a rational point, with exact control of the
values of the two coefficients.
-/
theorem exists_coordinate_decomposition_with_partialAt
    {f : BivariatePolynomial K} (p : RationalPoint f)
    (g : BivariatePolynomial K) :
    ∃ u v : BivariatePolynomial K,
      g - MvPolynomial.C (polynomialEval p g) =
          (MvPolynomial.X 0 - MvPolynomial.C (p.coords 0)) * u +
            (MvPolynomial.X 1 - MvPolynomial.C (p.coords 1)) * v ∧
        polynomialEval p u =
          polynomialEval p (MvPolynomial.pderiv 0 g) ∧
        polynomialEval p v =
          polynomialEval p (MvPolynomial.pderiv 1 g) := by
  induction g using MvPolynomial.induction_on with
  | C c =>
      refine ⟨0, 0, ?_, ?_, ?_⟩
      · simp [polynomialEval]
      · simp [polynomialEval]
      · simp [polynomialEval]
  | add g h hg hh =>
      obtain ⟨ug, vg, hg_decomp, hug, hvg⟩ := hg
      obtain ⟨uh, vh, hh_decomp, huh, hvh⟩ := hh
      refine ⟨ug + uh, vg + vh, ?_, ?_, ?_⟩
      · simp only [map_add]
        calc
          g + h -
              (MvPolynomial.C (polynomialEval p g) +
                MvPolynomial.C (polynomialEval p h)) =
              (g - MvPolynomial.C (polynomialEval p g)) +
                (h - MvPolynomial.C (polynomialEval p h)) := by ring
          _ = _ := by rw [hg_decomp, hh_decomp]; ring
      · simp only [map_add]
        rw [hug, huh]
      · simp only [map_add]
        rw [hvg, hvh]
  | mul_X g i hg =>
      obtain ⟨u, v, hdecomp, hu, hv⟩ := hg
      by_cases hi : i = 0
      · subst i
        refine
          ⟨MvPolynomial.X 0 * u +
              MvPolynomial.C (polynomialEval p g),
            MvPolynomial.X 0 * v, ?_, ?_, ?_⟩
        · simp only [map_mul, polynomialEval_X]
          linear_combination MvPolynomial.X 0 * hdecomp
        · rw [MvPolynomial.pderiv_mul]
          simp only [map_add, map_mul, polynomialEval_X,
            MvPolynomial.pderiv_X_self, mul_one]
          rw [hu]
          simp [polynomialEval]
          ring
        · rw [MvPolynomial.pderiv_mul]
          simp only [map_mul, polynomialEval_X,
            MvPolynomial.pderiv_X_of_ne
              (by decide : (0 : Fin 2) ≠ 1),
            mul_zero, add_zero]
          rw [hv]
          ring
      · have hi' : i = 1 := by
          apply Fin.ext
          omega
        subst i
        refine
          ⟨MvPolynomial.X 1 * u,
            MvPolynomial.X 1 * v +
              MvPolynomial.C (polynomialEval p g), ?_, ?_, ?_⟩
        · simp only [map_mul, polynomialEval_X]
          linear_combination MvPolynomial.X 1 * hdecomp
        · rw [MvPolynomial.pderiv_mul]
          simp only [map_mul, polynomialEval_X,
            MvPolynomial.pderiv_X_of_ne
              (by decide : (1 : Fin 2) ≠ 0),
            mul_zero, add_zero]
          rw [hu]
          ring
        · rw [MvPolynomial.pderiv_mul]
          simp only [map_add, map_mul, polynomialEval_X,
            MvPolynomial.pderiv_X_self, mul_one]
          rw [hv]
          simp [polynomialEval]
          ring

end AffinePlaneCurve
end Chapter06
end FieldArithmetic
