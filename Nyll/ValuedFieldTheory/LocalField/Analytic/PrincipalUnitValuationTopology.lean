/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.AdicProdiscreteComparison
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete

/-!
# The valuation topology on principal units is the adic topology

The comparison uses the actual valuation topology and does not require a
finite residue field. The valued-field structure is fixed once in the context.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
variable [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
  (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))]

open CompleteDVF.higherPrincipalUnitGroup

/-- The inherited topology on principal units equals their intrinsic adic topology. -/
theorem principalUnit_valuationTopology_eq_adic :
    (inferInstance : TopologicalSpace
      (Additive (CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation (Valued.v : _root_.Valuation K
          (WithZero (Multiplicative ℤ)))) 1))) =
      principalUnitAdicTopology (completeDVFOfWithZeroValuation
        (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))) := by
  let F := completeDVFOfWithZeroValuation
    (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
  let π : F.valuationSubring := chosenPrincipalUnitPadicUniformizer F
  have hmax : (inferInstance : TopologicalSpace F.valuationSubring) =
      F.maximalIdeal.adicTopology :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic
      (K := K) (Gamma := WithZero (Multiplicative ℤ))
  have hideal : LubinTate.Valuations.uniformizerPowerIdeal π 1 = F.maximalIdeal := by
    rw [LubinTate.Valuations.uniformizerPowerIdeal, pow_one,
      ← F.maximalIdeal_eq_span_uniformizer (chosenPrincipalUnitPadicUniformizer_isUniformizer F)]
  let carrierTopology (t : TopologicalSpace F.valuationSubring) :
      TopologicalSpace (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    let : TopologicalSpace F.valuationSubring := t
    inferInstance
  change carrierTopology (inferInstance : TopologicalSpace F.valuationSubring) =
    carrierTopology (LubinTate.Valuations.uniformizerPowerIdeal π 1).adicTopology
  rw [hideal]
  exact congrArg carrierTopology hmax

/-- The adic model is continuously additively equivalent to the actual principal units. -/
noncomputable def principalUnitAdicContinuousAddEquiv :
    AdicPrincipalUnits (completeDVFOfWithZeroValuation
      (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))) ≃ₜ+
    Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation
      (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))) 1) := by
  let F := completeDVFOfWithZeroValuation
    (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
  refine { AdicPrincipalUnits.addEquiv F with
    continuous_toFun := ?_, continuous_invFun := ?_ }
  · change @Continuous (AdicPrincipalUnits F)
      (Additive (CompleteDVF.higherPrincipalUnitGroup F 1))
      inferInstance inferInstance (AdicPrincipalUnits.equiv F)
    rw [principalUnit_valuationTopology_eq_adic (K := K)]
    exact continuous_induced_dom
  · change @Continuous (Additive (CompleteDVF.higherPrincipalUnitGroup F 1))
      (AdicPrincipalUnits F) inferInstance inferInstance (AdicPrincipalUnits.equiv F).symm
    rw [principalUnit_valuationTopology_eq_adic (K := K)]
    exact continuous_induced_rng.2 (continuous_id_of_le le_rfl)

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
