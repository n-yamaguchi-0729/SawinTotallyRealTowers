/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Tactic.Abel

/-!
# The ring identity for a commutator difference
-/

@[expose] public section

namespace ClassFieldTower.ProP

/-- A ring identity underlying the commutator filtration calculation. -/
theorem commutatorDifference_identity
    {R : Type*} [Ring R] (a b ai bi : R)
    (hai : a * ai = 1) (hbi : b * bi = 1) :
    a * b * ai * bi - 1 =
      ((a - 1) * (b - 1) - (b - 1) * (a - 1)) * ai * bi := by
  have hdiff : (a - 1) * (b - 1) - (b - 1) * (a - 1) = a * b - b * a := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  rw [hdiff]
  simp only [sub_mul]
  rw [mul_assoc b a ai, hai, mul_one, hbi]

end ClassFieldTower.ProP
