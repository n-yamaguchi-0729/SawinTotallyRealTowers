/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFEmbedding
import Mathlib.Data.Int.WithZero
import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Continuity for an extension of discrete valuations

The uniformly continuous map on the `WithVal` models is transported to the
actual valuation topologies on the original fields. No completion, finite
degree, or choice of normalized absolute value is required.
-/

namespace ValuationTheory.DiscreteValuationField.Valuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An extension of discrete valuations makes the algebra map continuous
for the actual topologies induced by the two valuations. -/
theorem continuous_algebraMap_of_hasExtension
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ)))
    [vK.IsRankOneDiscrete] [vL.IsRankOneDiscrete] [vK.HasExtension vL] :
    @Continuous K L (Valued.mk' vK).toUniformSpace.toTopologicalSpace
      (Valued.mk' vL).toUniformSpace.toTopologicalSpace (algebraMap K L) := by
  let base : DVF K := { ValueGroup := WithZero (Multiplicative ℤ), valuation := vK }
  let target : DVF L := { ValueGroup := WithZero (Multiplicative ℤ), valuation := vL }
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' vK
  let : Valued L (WithZero (Multiplicative ℤ)) := Valued.mk' vL
  let eK : WithVal vK ≃ᵤ K :=
    WithVal.uniformEquiv (v := vK) (w := vK) rfl _root_.Valuation.IsEquiv.refl
  let eL : WithVal vL ≃ᵤ L :=
    WithVal.uniformEquiv (v := vL) (w := vL) rfl _root_.Valuation.IsEquiv.refl
  exact eL.continuous.comp
    ((DVF.withValMap_uniformContinuous base target).continuous.comp eK.symm.continuous)

end ValuationTheory.DiscreteValuationField.Valuation
