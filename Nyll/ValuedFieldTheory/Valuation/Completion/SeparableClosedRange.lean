/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Algebra.Algebra.Tower

/-!
# Separable elements lie in an embedded separably closed field

An embedding from a separably closed field contains every element that is
separable over the common base, without any algebraicity assumption on the
ambient extension or on the separably closed field over that base.
-/

namespace ValuationTheory.Completion

variable {K S E : Type*} [Field K] [Field S] [Field E]
  [Algebra K S] [Algebra K E] [IsSepClosed S]

/-- An element separable over the common base lies in the image of every
embedding from a separably closed field. -/
theorem mem_fieldRange_of_isSeparable_of_isSepClosed
    (i : S →ₐ[K] E) {x : E} (hx : IsSeparable K x) : x ∈ i.fieldRange := by
  let : Algebra S E := i.toRingHom.toAlgebra
  have hxS : x ∈ separableClosure S E := IsSeparable.tower_top S hx
  have hbot : separableClosure S E = ⊥ :=
    IntermediateField.eq_bot_of_isSepClosed_of_isSeparable (separableClosure S E)
  rw [hbot] at hxS
  exact AlgHom.mem_fieldRange.mpr (IntermediateField.mem_bot.mp hxS)

end ValuationTheory.Completion
