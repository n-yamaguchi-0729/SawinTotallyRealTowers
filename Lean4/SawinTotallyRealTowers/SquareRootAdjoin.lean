/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

set_option autoImplicit false

/-!
# Adjoining a square root of a nonsquare

Over any base field, a square root of a nonsquare has minimal polynomial
`X² - a` and generates an extension of degree two. No assumption on the
characteristic or on the ambient extension is required.
-/

open Polynomial

universe u v

namespace ClassFieldTower.Sawin

/-- A square root of a nonsquare has the indicated minimal polynomial. -/
theorem minpoly_squareRoot_of_not_isSquare
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    (a : F) (α : Ω) (hSquare : α ^ 2 = algebraMap F Ω a) (ha : ¬ IsSquare a) :
    minpoly F α = X ^ 2 - C a := by
  apply Eq.symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    exact ha ((isSquare_iff_exists_sq a).mpr ⟨b, hb.symm⟩)
  · rw [map_sub, map_pow, aeval_X, aeval_C, hSquare, sub_self]
  · exact monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0)

/-- Adjoining a square root of a nonsquare gives a field of degree two. -/
theorem finrank_adjoin_squareRoot
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    (a : F) (α : Ω) (hSquare : α ^ 2 = algebraMap F Ω a) (ha : ¬ IsSquare a) :
    Module.finrank F (IntermediateField.adjoin F ({α} : Set Ω)) = 2 := by
  have hIntegral : IsIntegral F α := by
    refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0), ?_⟩
    rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hSquare, sub_self]
  rw [IntermediateField.adjoin.finrank hIntegral,
    minpoly_squareRoot_of_not_isSquare F Ω a α hSquare ha, natDegree_X_pow_sub_C]

/-- The actual simple intermediate field supplies the quadratic-extension
class, and hence finite dimensionality, at later algebraic boundaries. -/
theorem isQuadraticExtension_adjoin_squareRoot
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    (a : F) (α : Ω) (hSquare : α ^ 2 = algebraMap F Ω a) (ha : ¬ IsSquare a) :
    Algebra.IsQuadraticExtension F (IntermediateField.adjoin F ({α} : Set Ω)) where
  finrank_eq_two' := finrank_adjoin_squareRoot F Ω a α hSquare ha

/-- The canonical internal generator retains the square equation. -/
theorem adjoinSquareRoot_gen_sq
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    (a : F) (α : Ω) (hSquare : α ^ 2 = algebraMap F Ω a) :
    IntermediateField.AdjoinSimple.gen F α ^ 2 =
      algebraMap F (IntermediateField.adjoin F ({α} : Set Ω)) a := by
  apply (algebraMap (IntermediateField.adjoin F ({α} : Set Ω)) Ω).injective
  rw [map_pow, ← IsScalarTower.algebraMap_apply F
    (IntermediateField.adjoin F ({α} : Set Ω)) Ω]
  exact hSquare

/-- The canonical internal generator generates the whole simple extension. -/
theorem adjoinSquareRoot_gen_adjoin
    (F : Type u) (Ω : Type v) [Field F] [Field Ω] [Algebra F Ω]
    (α : Ω) :
    IntermediateField.adjoin F ({IntermediateField.AdjoinSimple.gen F α} :
      Set (IntermediateField.adjoin F ({α} : Set Ω))) = ⊤ := by
  apply IntermediateField.lift_injective (IntermediateField.adjoin F ({α} : Set Ω))
  rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
  rfl

end ClassFieldTower.Sawin
