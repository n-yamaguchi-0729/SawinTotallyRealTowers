/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableClosure
import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NormedModel
import Nyll.ValuedFieldTheory.Valuation.Henselian.RingEquiv

/-!
# Separable algebraic closedness in the completion of a Henselian DVF

The normed model comes from the given discrete valuation. Its unit ball is
isomorphic to the original Henselian valuation ring, so the normed completion
theorem applies to the actual valuation completion.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

universe u v

variable {K : Type u} [Field K]

/-- A Henselian discretely valued field is separably algebraically closed in
its valuation completion. No completeness or residue-field finiteness is assumed. -/
theorem exists_completion_eq_of_isSeparable (base : HenselianDVF.{u, v} K)
    (a : base.valuation.Completion) (ha : IsSeparable K a) :
    ∃ k : K, (k : base.valuation.Completion) = a := by
  have : (Valued.v : _root_.Valuation (WithVal base.valuation)
      base.ValueGroup).IsRankOneDiscrete :=
    Valuation.isRankOneDiscrete_comap_ringEquiv base.valuation (WithVal.equiv base.valuation)
  let : (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup).RankOne :=
    _root_.Valuation.IsRankOneDiscrete.rankOne
      (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup)
      (e := 2) (by norm_num)
  let : NontriviallyNormedField (WithVal base.valuation) :=
    Valued.toNontriviallyNormedField (WithVal base.valuation) base.ValueGroup
  have : HenselianRing
      (NormedField.valuation (K := WithVal base.valuation)).valuationSubring
      (IsLocalRing.maximalIdeal
        (NormedField.valuation (K := WithVal base.valuation)).valuationSubring) :=
    Henselian.henselianRing_maximalIdeal_of_ringEquiv
      (base.toDVF.normedWithValValuationSubringEquiv).symm
  obtain ⟨k, hk⟩ := Henselian.exists_completion_eq_of_isSeparable a
    (ha.tower_top (WithVal base.valuation))
  exact ⟨WithVal.equiv base.valuation k, hk⟩

end ValuationTheory.DiscreteValuationField.HenselianDVF
