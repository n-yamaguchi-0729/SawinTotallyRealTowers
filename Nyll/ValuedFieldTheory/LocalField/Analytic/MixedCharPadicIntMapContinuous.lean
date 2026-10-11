/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMap
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.PadicReductionContinuous
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete
import Mathlib.Topology.Algebra.Group.Basic

/-!
# Continuity of the p-adic integer map into a complete valued field

The lifted map carries the open kernel of reduction modulo `p^n` into the
`n`th maximal-ideal power. The adic topology on the valuation ring is its
actual subtype topology, so the map to the field is continuous.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

open scoped Topology

universe u

variable {K : Type u} [Field K]

/-- The actual map from p-adic integers is continuous in the valuation topology. -/
theorem continuous_padicIntToFieldOfMixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    @Continuous ℤ_[p] K (inferInstance : TopologicalSpace ℤ_[p])
      (Valued.mk' v).toUniformSpace.toTopologicalSpace (padicIntToFieldOfMixedChar v p) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have : IsTopologicalRing v.valuationSubring :=
    Subring.instIsTopologicalRing v.valuationSubring.toSubring
  have hadic : IsAdic (IsLocalRing.maximalIdeal v.valuationSubring) :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdic
  have hcontinuous : Continuous (padicIntToValuationSubringOfMixedChar v p) := by
    apply continuous_of_continuousAt_zero (padicIntToValuationSubringOfMixedChar v p)
    rw [ContinuousAt, map_zero, hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro n _
    have hkernel :
        ((RingHom.ker (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)) :
          Ideal ℤ_[p]) : Set ℤ_[p]) ∈ 𝓝 (0 : ℤ_[p]) :=
      (CompleteDVF.higherPrincipalUnitGroup.isOpen_ker_padicIntToZModPow p n).mem_nhds
        (RingHom.ker (PadicInt.toZModPow n)).zero_mem
    filter_upwards [hkernel] with a ha
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [padicIntToValuationSubringOfMixedChar_mod_pow]
    change PadicInt.toZModPow n a = 0 at ha
    rw [ha, ZMod.cast_zero]
  exact continuous_subtype_val.comp hcontinuous

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
