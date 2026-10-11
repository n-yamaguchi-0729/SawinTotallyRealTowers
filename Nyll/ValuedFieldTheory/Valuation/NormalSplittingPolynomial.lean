/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Normal.Basic

/-!
# Nonzero splitting polynomials for finite normal extensions

A finite normal extension is the splitting field of a nonzero polynomial.
If the polynomial supplied by the standard existence theorem is zero, the
constant polynomial one has the same empty root set and generates the same
extension.
-/

namespace Normal

/-- A finite normal extension admits a nonzero splitting polynomial. -/
theorem exists_ne_zero_isSplittingField
    (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Normal F K] [FiniteDimensional F K] :
    ∃ f : Polynomial F, f ≠ 0 ∧ Polynomial.IsSplittingField F K f := by
  obtain ⟨f, hsplit⟩ := Normal.exists_isSplittingField F K
  rcases eq_or_ne f 0 with rfl | hf
  · refine ⟨1, one_ne_zero, { splits' := ?_, adjoin_rootSet' := ?_ }⟩
    · rw [Polynomial.map_one]
      exact Polynomial.Splits.one
    · simpa only [Polynomial.rootSet_zero, Polynomial.rootSet_one] using
        hsplit.adjoin_rootSet'
  · exact ⟨f, hf, hsplit⟩

end Normal
