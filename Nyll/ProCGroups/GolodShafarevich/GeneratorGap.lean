/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Basic

/-!
# The numerical Golod--Shafarevich gap used by the Martinet seed

This is the arithmetic step that turns a 3-class rank of at least six and the
Shafarevich upper bound `r <= d + 2` into the non-strict inequality needed to
contradict the finite Golod--Shafarevich bound.
-/

namespace ClassFieldTower.Martinet

/-- For generator rank at least six, four times the Shafarevich upper bound
`d + 2` is at most the square of the generator rank. -/
theorem four_mul_add_two_le_sq {d : ℕ} (hd : 6 ≤ d) :
    4 * (d + 2) ≤ d ^ 2 := by
  calc
    4 * (d + 2) = 4 * d + 8 := by omega
    _ ≤ 6 * d := by omega
    _ ≤ d * d := Nat.mul_le_mul_right d hd
    _ = d ^ 2 := (Nat.pow_two d).symm

end ClassFieldTower.Martinet
