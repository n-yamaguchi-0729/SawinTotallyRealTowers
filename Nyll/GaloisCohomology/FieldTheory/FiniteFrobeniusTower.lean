/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Frobenius in towers of finite constant fields

Changing the finite ground field replaces its arithmetic Frobenius by the
power given by the extension degree, on the same actual algebraic extension.
-/

@[expose] public section

noncomputable section

namespace FiniteField

variable (k E Ω : Type*) [Field k] [Fintype k] [Field E] [Fintype E] [Algebra k E]
    [Field Ω] [Algebra k Ω] [Algebra E Ω] [IsScalarTower k E Ω]
    [Algebra.IsAlgebraic k Ω] [Algebra.IsAlgebraic E Ω]

/-- Arithmetic Frobenius over a larger finite constant field is the degree power of Frobenius. -/
theorem frobeniusAlgEquiv_restrictScalars :
    (frobeniusAlgEquivOfAlgebraic E Ω).restrictScalars k =
      (frobeniusAlgEquivOfAlgebraic k Ω) ^ Module.finrank k E := by
  have hcard : Fintype.card E = Fintype.card k ^ Module.finrank k E := by
    simpa only [Nat.card_eq_fintype_card] using (Module.natCard_eq_pow_finrank (K := k) (V := E))
  ext x
  change x ^ Fintype.card E = ((frobeniusAlgEquivOfAlgebraic k Ω) ^ Module.finrank k E) x
  rw [AlgEquiv.coe_pow, coe_frobeniusAlgEquivOfAlgebraic_iterate, hcard]

end FiniteField
