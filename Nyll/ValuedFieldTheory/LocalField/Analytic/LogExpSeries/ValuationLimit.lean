/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Int.WithZero
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Non-strict valuation bounds at a limit

An eventual upper bound on a convergent sequence remains an upper bound
on its limit. The bound need not be nonzero or occur as a value of the valuation.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

open Filter
open scoped Topology

variable {K : Type*} [Field K]

/-- A non-strict valuation bound passes to the limit, including radius zero. -/
theorem valuation_limit_le_of_tendsto_of_eventually_le
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    {γ : WithZero (Multiplicative ℤ)} {u : ℕ → K} {z : K}
    (hu : Tendsto u atTop (@nhds K (Valued.mk' v).toUniformSpace.toTopologicalSpace z))
    (hsmall : ∀ᶠ n : ℕ in atTop, v (u n) ≤ γ) : v z ≤ γ := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  by_contra hz
  have hγz : γ < v z := lt_of_not_ge hz
  have hvz : v z ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le hγz)
  have hdiff : Tendsto (fun n : ℕ => z - u n) atTop (𝓝 (0 : K)) := by
    have hc : Tendsto (fun n : ℕ => z) atTop (𝓝 z) := tendsto_const_nhds
    simpa only [sub_self] using hc.sub hu
  have hball : {w : K | v w < v z} ∈ 𝓝 (0 : K) := by
    rw [Valued.mem_nhds_zero]
    refine ⟨Units.mk0 (v.restrict z) (v.restrict_eq_zero_iff.not.mpr hvz), ?_⟩
    intro w hw
    change v.restrict w < v.restrict z at hw
    exact v.restrict_lt_iff.mp hw
  have hdiff_small : ∀ᶠ n : ℕ in atTop, v (z - u n) < v z := hdiff.eventually hball
  obtain ⟨n, hn, hdn⟩ := (hsmall.and hdiff_small).exists
  have hsub : v (z - u n) = v z := v.map_sub_eq_of_lt_left (hn.trans_lt hγz)
  rw [hsub] at hdn
  exact (lt_irrefl (v z)) hdn

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
