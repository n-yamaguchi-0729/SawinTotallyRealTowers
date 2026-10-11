/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteSeparableGenerator
import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NormedModel
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# Descending generators from the actual completion of a DVF

The original valuation supplies a norm with the same uniformity on `WithVal`.
Its completion is therefore the given valuation completion. Density of the
canonical ground-field map then descends finite separable generators.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v w

variable {K : Type u} [Field K]

/-- Every finite separable extension of the actual valuation completion has
a generator separable over the original field, with the same degree.
The ground field need not be Henselian or complete. -/
theorem exists_completion_extension_generator (base : DVF.{u, v} K)
    (E : Type w) [Field E] [Algebra base.valuation.Completion E]
    [Algebra K E] [IsScalarTower K base.valuation.Completion E]
    [FiniteDimensional base.valuation.Completion E]
    [Algebra.IsSeparable base.valuation.Completion E] :
    ∃ γ : E, IsSeparable K γ ∧
      Algebra.adjoin base.valuation.Completion ({γ} : Set E) = ⊤ ∧
      (minpoly K γ).natDegree = Module.finrank base.valuation.Completion E := by
  have : (Valued.v : _root_.Valuation (WithVal base.valuation)
      base.ValueGroup).IsRankOneDiscrete :=
    Valuation.isRankOneDiscrete_comap_ringEquiv base.valuation (WithVal.equiv base.valuation)
  let : (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup).RankOne :=
    _root_.Valuation.IsRankOneDiscrete.rankOne
      (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup)
      (e := 2) (by norm_num)
  let : NontriviallyNormedField (WithVal base.valuation) :=
    Valued.toNontriviallyNormedField (WithVal base.valuation) base.ValueGroup
  let : NontriviallyNormedField base.valuation.Completion :=
    { (inferInstance : NormedField base.valuation.Completion) with
      non_trivial := by
        obtain ⟨k, hk⟩ := NormedField.exists_one_lt_norm (WithVal base.valuation)
        exact ⟨(k : base.valuation.Completion),
          (UniformSpace.Completion.norm_coe k).symm ▸ hk⟩ }
  have : IsUltrametricDist base.valuation.Completion :=
    IsUltrametricDist.of_normedAlgebra (WithVal base.valuation)
  exact Completion.exists_isSeparable_generator_of_denseRange (E := E)
    (WithVal.denseRange_algebraMap_completion base.valuation)

end ValuationTheory.DiscreteValuationField.DVF
