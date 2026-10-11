/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.HilbertPairingSymbol
import Nyll.ClassFieldTheory.Definitions.HilbertSymbols.IsKummerNorm

/-!
# The norm-residue criterion
-/



namespace ClassFieldTheory.HilbertPairing

universe u

/-- The symbol of `a` and `b` is one exactly when `b` is a norm from the
Kummer algebra of `a`. -/
def SatisfiesNormResidueCriterion
    {K : Type u} [Field K] {n : ℕ+}
    (B : HilbertPairing K n) : Prop :=
  ∀ a b : Kˣ, B.symbol a b = 1 ↔ IsKummerNorm K n a b

end ClassFieldTheory.HilbertPairing
