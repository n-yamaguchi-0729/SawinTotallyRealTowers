/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Completeness for the actual topology of an integer-valued DVF

The valuation ring is complete in its native subtype topology because that
topology is maximal-ideal adic. A compatible norm identifies this ring with
the closed unit ball, whose completeness implies completeness of the field.
The norm retains the original valuation uniformity. No residue-field
finiteness or local compactness is required.
-/

namespace ValuationTheory.DiscreteValuationField.Valuation

variable {K : Type*} [Field K]

/-- Adic completeness of an integer-valued discrete valuation supplies
completeness for the actual uniformity induced by that valuation. -/
theorem completeSpace_ofWithZeroValuation
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) [IsCompleteDiscrete v] :
    @CompleteSpace K (Valued.mk' v).toUniformSpace := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : v.RankOne :=
    _root_.Valuation.IsRankOneDiscrete.rankOne v (e := 2) (by norm_num)
  let : NormedField K := Valued.toNormedField K (WithZero (Multiplicative ℤ))
  have hadic : IsAdic (IsLocalRing.maximalIdeal v.valuationSubring) :=
    Valuations.rankOneDiscreteValuationSubring_isAdic
  have hring : CompleteSpace v.valuationSubring :=
    (hadic.isAdicComplete_iff.mp (isAdicComplete v)).1
  have hcomplete : IsComplete (v.valuationSubring : Set K) := by
    have h := (completeSpace_iff_isComplete_univ (α := v.valuationSubring)).mp hring
    rw [Subtype.isComplete_iff, Set.image_univ, Subtype.range_coe_subtype] at h
    exact h
  apply NormedField.completeSpace_iff_isComplete_closedBall.mpr
  rw [← Valued.toNormedField.setOfPred_mem_integer_eq_closedBall]
  exact hcomplete

end ValuationTheory.DiscreteValuationField.Valuation
