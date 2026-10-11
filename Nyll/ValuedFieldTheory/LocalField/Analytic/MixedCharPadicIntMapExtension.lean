/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMapContinuous
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationExtensionContinuous
import Mathlib.Topology.DenseEmbedding

/-!
# Compatibility of the actual p-adic integer maps under valued extensions

The two maps agree on natural numbers. Their continuity in the actual
valuation topologies extends this equality to all p-adic integers.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The constructed p-adic integer maps commute with an extension of
complete discrete valuations. -/
theorem map_padicIntToFieldOfMixedChar
    (vK : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (vL : _root_.Valuation L (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vK]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vL]
    [vK.HasExtension vL]
    (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField vK.valuationSubring) p]
    [CharP (IsLocalRing.ResidueField vL.valuationSubring) p]
    (a : ℤ_[p]) :
    algebraMap K L (padicIntToFieldOfMixedChar vK p a) =
      padicIntToFieldOfMixedChar vL p a := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' vK
  let : Valued L (WithZero (Multiplicative ℤ)) := Valued.mk' vL
  have hleft : Continuous (fun z : ℤ_[p] =>
      algebraMap K L (padicIntToFieldOfMixedChar vK p z)) :=
    (ValuationTheory.DiscreteValuationField.Valuation.continuous_algebraMap_of_hasExtension
      vK vL).comp (continuous_padicIntToFieldOfMixedChar vK p)
  have hclosed : IsClosed {z : ℤ_[p] |
      algebraMap K L (padicIntToFieldOfMixedChar vK p z) =
        padicIntToFieldOfMixedChar vL p z} :=
    isClosed_eq hleft (continuous_padicIntToFieldOfMixedChar vL p)
  refine PadicInt.denseRange_natCast.induction_on a hclosed ?_
  intro n
  simp only [map_natCast]

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
