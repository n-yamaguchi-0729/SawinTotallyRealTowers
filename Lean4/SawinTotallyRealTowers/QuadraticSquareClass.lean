/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.SquarefreeIntegralCoordinates
import SawinTotallyRealTowers.QuadraticBasis
import SawinTotallyRealTowers.QuadraticTrace
import Mathlib.Data.Int.Lemmas

set_option autoImplicit false

/-!
# Uniqueness of squarefree quadratic radicands

Two signed squarefree integers in the same rational square class agree.
Taking traces in a quadratic field shows that any two square-root generators
have squares in the same rational square class. Thus the normalized radicand
of a quadratic field is unique, including its sign.
-/

universe u

namespace ClassFieldTower.Sawin

/-- Signed squarefree integers representing the same rational square class
are equal; no positivity assumption is necessary. -/
theorem squarefree_int_eq_of_mul_rat_sq
    (d e : ℤ) (hd : Squarefree d.natAbs) (he : Squarefree e.natAbs)
    (q : ℚ) (h : (d : ℚ) = (e : ℚ) * q ^ 2) : d = e := by
  obtain ⟨n, hn⟩ := exists_int_eq_of_squarefree_mul_sq_eq_int e he q ⟨d, h.symm⟩
  have hInt : d = e * n ^ 2 := by
    apply Int.cast_injective (α := ℚ)
    simpa only [hn, Int.cast_mul, Int.cast_pow] using h
  have hAbs : d.natAbs = e.natAbs * n.natAbs ^ 2 := by
    simpa only [Int.natAbs_mul, Int.natAbs_pow] using congrArg Int.natAbs hInt
  have hDiv : n.natAbs ^ 2 ∣ d.natAbs :=
    ⟨e.natAbs, hAbs.trans (Nat.mul_comm e.natAbs (n.natAbs ^ 2))⟩
  have hUnit : IsUnit n.natAbs := by
    apply hd n.natAbs
    simpa only [pow_two] using hDiv
  have hOne : n.natAbs = 1 := Nat.isUnit_iff.mp hUnit
  have hSq : n ^ 2 = 1 := by
    simpa only [one_pow] using
      (Int.natAbs_eq_iff_sq_eq (a := n) (b := 1)).mp hOne
  rw [hInt, hSq, mul_one]

/-- Any two signed squarefree square-root generators of the same quadratic
extension have the same radicand. -/
theorem quadratic_squarefree_radicand_unique
    (L : Type u) [Field L] [Algebra ℚ L] [Algebra.IsQuadraticExtension ℚ L]
    (d e : ℤ) (hd : Squarefree d.natAbs) (he : Squarefree e.natAbs)
    (α β : L)
    (hαSquare : α ^ 2 = algebraMap ℚ L (d : ℚ))
    (hβSquare : β ^ 2 = algebraMap ℚ L (e : ℚ))
    (hαGenerate : IntermediateField.adjoin ℚ ({α} : Set L) = ⊤)
    (hβGenerate : IntermediateField.adjoin ℚ ({β} : Set L) = ⊤) : d = e := by
  obtain ⟨a, b, hα⟩ :=
    exists_rat_linear_combination_of_quadraticGenerator L β hβGenerate α
  have hTrace : 2 * a = 0 := by
    rw [← trace_quadratic_coordinates L (e : ℚ) a b β hβSquare hβGenerate, ← hα]
    exact trace_quadratic_generator L (d : ℚ) α hαSquare hαGenerate
  have ha : a = 0 := (mul_eq_zero.mp hTrace).resolve_left (by decide : (2 : ℚ) ≠ 0)
  have hClass : (d : ℚ) = (e : ℚ) * b ^ 2 := by
    apply (algebraMap ℚ L).injective
    calc
      algebraMap ℚ L (d : ℚ) = α ^ 2 := hαSquare.symm
      _ = algebraMap ℚ L ((e : ℚ) * b ^ 2) := by
        rw [hα, ha, map_zero, zero_add, mul_pow, hβSquare, map_mul, map_pow]
        exact mul_comm (algebraMap ℚ L b ^ 2) (algebraMap ℚ L (e : ℚ))
  exact squarefree_int_eq_of_mul_rat_sq d e hd he b hClass

end ClassFieldTower.Sawin
