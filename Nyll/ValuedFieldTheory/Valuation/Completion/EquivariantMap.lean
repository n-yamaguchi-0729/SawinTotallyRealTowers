/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFEmbedding
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteRingEquiv

/-!
# Equivariance of maps between discrete valued completions

A relative field automorphism carrying one prolongation to another induces
a completion isomorphism commuting with the map from the completed base field.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (base : DVF K) (source target : DVF L)
  [base.valuation.HasExtension source.valuation]
  [base.valuation.HasExtension target.valuation]

/-- The map induced by an extension of discrete valuations is continuous. -/
theorem completionMap_continuous : Continuous (completionMap base source) :=
  UniformSpace.Completion.continuous_map

/-- Completion isomorphisms induced by relative field automorphisms commute
with the embedding of the completed base field. -/
theorem completionRingEquiv_comp_completionMap
    (τ : Gal(L/K))
    (hτ : source.valuation.IsEquiv (target.valuation.comap τ.toRingEquiv.toRingHom)) :
    (completionRingEquiv source target τ.toRingEquiv hτ).toRingHom.comp
        (completionMap base source) = completionMap base target := by
  apply DFunLike.ext'
  have he : Continuous (completionRingEquiv source target τ.toRingEquiv hτ) :=
    UniformSpace.Completion.continuous_map
  apply UniformSpace.Completion.ext (he.comp (completionMap_continuous base source))
    (completionMap_continuous base target)
  intro x
  change completionRingEquiv source target τ.toRingEquiv hτ
    (completionMap base source ((WithVal.equiv base.valuation x : K) : base.valuation.Completion)) =
      completionMap base target ((WithVal.equiv base.valuation x : K) : base.valuation.Completion)
  rw [completionMap_coe_base, completionMap_coe_base]
  change completionRingEquiv source target τ.toRingEquiv hτ
    (algebraMap L source.valuation.Completion (algebraMap K L (WithVal.equiv base.valuation x))) =
      algebraMap L target.valuation.Completion (algebraMap K L (WithVal.equiv base.valuation x))
  rw [completionRingEquiv_algebraMap]
  exact congrArg (algebraMap L target.valuation.Completion)
    (τ.commutes (WithVal.equiv base.valuation x))

end ValuationTheory.DiscreteValuationField.DVF
