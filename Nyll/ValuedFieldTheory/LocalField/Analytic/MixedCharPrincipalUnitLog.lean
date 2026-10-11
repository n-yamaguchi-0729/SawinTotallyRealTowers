/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.WithZeroCompleteSpace

/-!
# The principal-unit logarithm in mixed characteristic

The logarithm is constructed on every complete mixed-characteristic discrete
valuation field, including fields with infinite residue field. Its scale and
the completeness of the actual valuation topology are supplied by the
valuation, rather than requested as comparison hypotheses.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The actual logarithm series as a homomorphism on all first principal units. -/
noncomputable def principalUnitLogOfMixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1 →*
      Multiplicative K :=
  principalUnitLogSeriesHomOfWithZeroValuationScaled (p := p) v
    (v.residueRamificationIndex p)
    (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    (fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
      (n + 1) (Nat.succ_ne_zero n))
    (ValuationTheory.DiscreteValuationField.Valuation.completeSpace_ofWithZeroValuation v)

/-- Evaluation agrees with the existing logarithm series. -/
@[simp] theorem principalUnitLogOfMixedChar_apply_toAdd
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    (principalUnitLogOfMixedChar v p u).toAdd =
      principalUnitLogSeriesOfWithZeroValuation v u
        (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)) := rfl

/-- The logarithm is continuous for the actual valuation topology. -/
theorem continuous_principalUnitLogOfMixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
    Continuous (principalUnitLogOfMixedChar v p) :=
  continuous_principalUnitLogSeriesHomOfWithZeroValuationScaled (p := p) v
    (v.residueRamificationIndex p)
    (fun n => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
    (fun n => v.natCast_eq_exp_neg_ramificationIndex_mul_padicValNat p
      (n + 1) (Nat.succ_ne_zero n))
    (ValuationTheory.DiscreteValuationField.Valuation.completeSpace_ofWithZeroValuation v)

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
