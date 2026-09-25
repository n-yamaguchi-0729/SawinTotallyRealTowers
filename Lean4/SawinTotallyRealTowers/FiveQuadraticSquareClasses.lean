/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false

/-!
# Five independent rational square classes

The radicands `5, 13, 17, 21, 33` have no nonempty square subproduct.
There are exactly thirty-one nonempty subsets. The natural-number check
uses the square-root decision procedure inside the Lean kernel; the
rational statement follows from the square criterion for natural casts.
-/

open scoped BigOperators

namespace ClassFieldTower.Sawin

/-- The five radicands used in the initial real multiquadratic layer. -/
def sawinQuadraticRadicand : Fin 5 → ℕ := ![5, 13, 17, 21, 33]

private theorem sawinQuadraticRadicand_nat_products_nonsquare :
    ∀ s : Finset (Fin 5), s.Nonempty →
      ¬ IsSquare (∏ i ∈ s, sawinQuadraticRadicand i) := by
  decide +kernel

/-- Every nonempty subproduct of the five radicands is nonsquare over ℚ. -/
theorem sawinQuadraticRadicand_product_nonsquare
    (s : Finset (Fin 5)) (hs : s.Nonempty) :
    ¬ IsSquare (∏ i ∈ s, (sawinQuadraticRadicand i : ℚ)) := by
  intro hSquare
  have hCast : ((∏ i ∈ s, sawinQuadraticRadicand i : ℕ) : ℚ) =
      ∏ i ∈ s, (sawinQuadraticRadicand i : ℚ) :=
    map_prod (Nat.castRingHom ℚ) sawinQuadraticRadicand s
  rw [← hCast] at hSquare
  exact sawinQuadraticRadicand_nat_products_nonsquare s hs
    (Rat.isSquare_natCast_iff.mp hSquare)

/-- Each of the five radicands defines a genuine quadratic extension of ℚ. -/
theorem sawinQuadraticRadicand_nonsquare (i : Fin 5) :
    ¬ IsSquare (sawinQuadraticRadicand i : ℚ) := by
  simpa only [Finset.prod_singleton] using
    sawinQuadraticRadicand_product_nonsquare {i} (Finset.singleton_nonempty i)

end ClassFieldTower.Sawin
