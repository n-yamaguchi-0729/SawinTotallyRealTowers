/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Discrete rank-one valuations under equivalence

Equivalent valuations on a field have the same discrete rank-one property.
-/

namespace Valuation

/-- Equivalent field valuations have the same discrete rank-one property. -/
theorem IsEquiv.isRankOneDiscrete
    {K Γ Δ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] [LinearOrderedCommGroupWithZero Δ]
    {v : Valuation K Γ} {w : Valuation K Δ} (h : v.IsEquiv w)
    [v.IsRankOneDiscrete] : w.IsRankOneDiscrete := by
  let e : v.valueGroup ≃* w.valueGroup :=
    WithZero.unitsWithZeroEquiv.symm.trans
      ((Units.mapEquiv h.orderMonoidIso.toMulEquiv).trans WithZero.unitsWithZeroEquiv)
  have : w.IsNontrivial := h.isNontrivial_iff.mp inferInstance
  have : IsCyclic w.valueGroup := isCyclic_of_surjective e.toMonoidHom e.surjective
  exact IsRankOneDiscrete.mk' w

end Valuation
