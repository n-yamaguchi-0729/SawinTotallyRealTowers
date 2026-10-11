/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.NormalizedCompleteExtension
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.CharP.Algebra

/-!
# Complete extension valuations with the base residue characteristic

A finite separable extension receives an integer-valued complete discrete
valuation. The induced embedding of residue fields preserves characteristic.
-/

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

/-- A finite separable extension has a complete integer-valued valuation
extending the given valuation and with the same residue characteristic. -/
theorem exists_complete_valuation_of_finite_separable_of_residueChar
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete vF] (n : ℕ)
    [hres : CharP (IsLocalRing.ResidueField vF.valuationSubring) n] :
    ∃ vE : _root_.Valuation E (WithZero (Multiplicative ℤ)),
      Valuation.IsCompleteDiscrete vE ∧ vF.HasExtension vE ∧
        CharP (IsLocalRing.ResidueField vE.valuationSubring) n := by
  let base : CompleteDVF F :=
    { ValueGroup := WithZero (Multiplicative ℤ), valuation := vF }
  obtain ⟨vE, hcomplete, hext⟩ :=
    exists_normalized_complete_valuation_of_finite_separable (L := E) base
  refine ⟨vE, hcomplete, hext, ?_⟩
  exact (Algebra.charP_iff (IsLocalRing.ResidueField vF.valuationSubring)
    (IsLocalRing.ResidueField vE.valuationSubring) n).mp hres

end ValuationTheory.DiscreteValuationField.ValuedExtension
