/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
public import Nyll.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv

/-!
# Field values of the existing deep exponential and logarithm

The algebraic equivalence and its evaluated series formulas are independent
of a choice of p-adic field. Their existing namespace and maps are preserved.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory.Padic

open LocalFieldTheory ValuationTheory

open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
  (completeDVFOfWithZeroValuation) in
/-- At a depth in the convergence range, exponential and logarithm identify
the multiplicative maximal-ideal power with the higher principal units. -/
noncomputable def expLogMulEquivOfWithZeroValuation
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) (n : ℕ)
    (hlevel :
      (DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v : ℚ) /
          (((DiscreteValuationField.LocalField.ofWithZeroValuation v).residueCharacteristic : ℚ)
            - 1) <
        (n : ℚ)) :
    Multiplicative
        ((DiscreteValuationField.MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation
          v).maximalIdeal ^ n :
          Ideal
            (completeDVFOfWithZeroValuation v).valuationSubring) ≃*
      DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
        (DiscreteValuationField.MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v)
        n := by
  letI : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let P :=
    DiscreteValuationField.MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv
      v hv n hlevel
  refine
    { toFun := fun a => P a
      invFun := fun u => P.symm u
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · exact P.left_inv
  · exact P.right_inv
  · exact P.map_mul

open _root_.LocalFieldTheory.DiscreteValuationField.LocalField
  (valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat) in
open _root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
  (principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled
   principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled
   principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled) in
open _root_.LocalFieldTheory.DiscreteValuationField.WithZeroValuation
  (exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective) in
/-- The underlying field value of the exponential/logarithm equivalence is
given by the evaluated exponential series. -/
theorem expLogMulEquivOfWithZeroValuation_fieldVal
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) (n : ℕ)
    (hlevel :
      (DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v : ℚ) /
          (((DiscreteValuationField.LocalField.ofWithZeroValuation v).residueCharacteristic : ℚ)
            - 1) <
        (n : ℚ))
    (a : Multiplicative
      ((DiscreteValuationField.MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation
        v).maximalIdeal ^ n :
        Ideal
          (DiscreteValuationField.MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation
          v).valuationSubring)) :
    let F :=
      DiscreteValuationField.MultiplicativeIntegerValuation.completeDVFOfWithZeroValuation v
    let E := expLogMulEquivOfWithZeroValuation v hv n hlevel
    ((((E a : DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup F n) :
      F.valuationSubringˣ) :
        F.valuationSubring) : K) =
      DiscreteValuationField.MultiplicativeIntegerValuation.expSeriesFieldOfWithZeroValuation
        v (((a.toAdd : F.valuationSubring) : K))
          (fun m =>
            Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let p : ℕ :=
    (LocalFieldTheory.DiscreteValuationField.LocalField.ofWithZeroValuation v).residueCharacteristic
  let _ : Fact p.Prime := by
    dsimp [p]
    infer_instance
  simp only [expLogMulEquivOfWithZeroValuation]
  simp only [
    DiscreteValuationField.MultiplicativeIntegerValuation.chosenExpLogContinuousMulEquiv,
    principalUnitExpLogContinuousMulEquivOfExact_ofWithZeroValuationScaled,
    principalUnitExpLogMulEquivOfExact_ofWithZeroValuationScaled]
  apply
    principalUnitExpSeries_maximalIdealPow_val_ofWithZeroValuationScaled
      (v := v) (p := p)
      (LocalFieldTheory.DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v)
      n
  case hπval =>
    exact Classical.choose_spec
      (exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
        v hv)
  case hπ =>
    exact
      DiscreteValuationField.WithZeroValuation.isUniformizer_of_valuation_eq_exp_neg_one
        v _
        (Classical.choose_spec
          (exists_valuationSubring_valuation_eq_exp_neg_one_of_surjective
            v hv))
  case hlevel => exact hlevel
  case hnval =>
    intro m
    exact
      valuation_natCast_factorial_eq_exp_neg_ramificationIndex_mul_padicValNat
        v m
  case hcomplete =>
    exact
      DiscreteValuationField.WithZeroValuationTopology.completeSpace_ofWithZeroValuation
        v

open DiscreteValuationField.MultiplicativeIntegerValuation in
/-- The inverse of the existing deep equivalence evaluates to the same
logarithm series used in the norm–trace identity. -/
theorem expLogMulEquivOfWithZeroValuation_symm_fieldVal
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    [Finite (IsLocalRing.ResidueField v.valuationSubring)] [CharZero K]
    (hv : Function.Surjective v) (n : ℕ)
    (hlevel :
      (DiscreteValuationField.LocalField.ramificationIndexOfWithZeroValuation v : ℚ) /
          (((DiscreteValuationField.LocalField.ofWithZeroValuation v).residueCharacteristic : ℚ)
            - 1) < (n : ℚ))
    (a : DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) n) :
    let F := completeDVFOfWithZeroValuation v
    ((((expLogMulEquivOfWithZeroValuation v hv n hlevel).symm a).toAdd :
        F.valuationSubring) : K) =
      logOnePlusSeriesFieldOfWithZeroValuation v
        ((((a : F.valuationSubringˣ) : F.valuationSubring) : K) - 1)
        (fun m => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)) := by
  rfl

end LocalFieldTheory.Padic
