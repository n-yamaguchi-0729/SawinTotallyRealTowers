/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.AutomorphismEquivariance
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismEquiv

/-!
# Equivariance of the mixed-characteristic principal-unit logarithm

A valuation-preserving field automorphism acts on the actual principal-unit
group, and its field action commutes with the logarithm of that unit. Both
the action and the continuity used to transport the infinite sum are supplied
by the preceding constructions.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The principal-unit logarithm commutes with the actual induced automorphism. -/
theorem principalUnitLogOfMixedChar_equivOfPreserves
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (f : K ≃+* K) (hval : ∀ x : K, v (f x) = v x)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    (principalUnitLogOfMixedChar v p
      (CompleteDVF.higherPrincipalUnitGroup.equivOfPreserves
        (completeDVFOfWithZeroValuation v) f
        (fun x => by change v x ≤ 1 ↔ v (f x) ≤ 1; rw [hval x]) 1 u)).toAdd =
      f (principalUnitLogOfMixedChar v p u).toAdd := by
  rw [principalUnitLogOfMixedChar_apply_toAdd, principalUnitLogOfMixedChar_apply_toAdd]
  simp only [principalUnitLogSeriesOfWithZeroValuation]
  rw [map_logOnePlusSeriesField_of_preserves v f hval]
  congr 1
  simp only [principalUnitSubOneOfWithZeroValuation,
    CompleteDVF.higherPrincipalUnitGroup.equivOfPreserves_apply_coe,
    _root_.map_sub, _root_.map_one]

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
