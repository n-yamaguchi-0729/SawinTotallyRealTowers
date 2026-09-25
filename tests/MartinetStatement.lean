/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Statement adapted from Lean Eval:
https://github.com/leanprover/lean-eval/blob/6b4b87b672f5301f24983a12fda65dac608453ce/generated/martinet_totally_real_towers/Challenge.lean
Lean Eval repository: Copyright 2026 Lean FRO, LLC; Apache 2.0.
-/

import SawinTotallyRealTowers.MartinetCorollary

set_option autoImplicit false

open NumberField

/-- Exact Lean Eval `martinet_totally_real_towers` target, via the public corollary. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  ClassFieldTower.Sawin.exists_totallyReal_discr_le
