/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
import Nyll.ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization

/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

The coefficient selected in `RecursiveCoefficient` is inserted as a single
monomial.  This file proves that the insertion preserves the prescribed linear
term and cancels the defect coefficient in precisely that total degree.
-/



noncomputable section

open scoped BigOperators

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The single monomial inserted at one step of the recursive construction. -/
noncomputable def monomialCorrection
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.monomial d
    (correctionCoefficient hπ e ebar hH d hd)

/-- Insert the recursive correction into the current approximation. -/
noncomputable def correctedIntertwiner
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  H + monomialCorrection hπ e ebar hH d hd

/-- A correction in total degree at least two does not change the prescribed
linear term. -/
theorem correctedIntertwiner_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L := by
  classical
  rw [correctedIntertwiner, HasLinearTerm]
  have hd' : (2 : ℕ∞) ≤ (d.degree : ℕ∞) := by
    exact_mod_cast hd
  have hcorrection :
      (2 : ℕ∞) ≤ (monomialCorrection hπ e ebar hH d hd).order := by
    rw [monomialCorrection, MvPowerSeries.order_monomial]
    split_ifs
    · exact le_top
    · exact hd'
  rw [show
    H + monomialCorrection hπ e ebar hH d hd - linearForm L =
      (H - linearForm L) +
        monomialCorrection hπ e ebar hH d hd by ring]
  exact
    (le_min hH hcorrection).trans
      MvPowerSeries.min_order_le_add

/-- The recursively selected degree-`d` monomial cancels the degree-`d`
coefficient of the intertwining defect. -/
theorem coeff_defect_correctedIntertwiner_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries.coeff d
        (defect e ebar
          (correctedIntertwiner hπ e ebar hH d hd)) = 0 := by
  rw [
    correctedIntertwiner,
    monomialCorrection,
    coeff_defect_add_monomial_eq_of_degree_le e ebar hH d d le_rfl hd,
    ite_eq_left rfl,
    ← uniformizer_mul_normalizedDefectCoefficient hπ e ebar hH d,
    correctionCoefficient_spec hπ e ebar hH d hd]
  ring

end SameUniformizer
end LubinTate

end
