/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalExact
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalModule
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

/-!
# The ideal-square radical over the rationals

Class number one makes the actual unit-to-radical map surjective.
The integral units of the rationals are ±1, so these two representatives
exhaust the ideal-square radical. This identifies its unique possible
obstruction coordinate without assuming a dimension bound or a comparison.
-/

open NumberField IsDedekindDomain
open scoped NumberField

namespace ClassFieldTower.Sawin
open ClassFieldTower.Martinet.Shafarevich

private theorem rationalRingUnit_eq_one_or_neg_one (u : (𝓞 ℚ)ˣ) :
    u = 1 ∨ u = -1 := by
  let e : (𝓞 ℚ)ˣ ≃* ℤˣ := Units.mapEquiv Rat.ringOfIntegersEquiv.toMulEquiv
  rcases Int.units_eq_one_or (e u) with h | h
  · exact Or.inl (e.injective (h.trans (map_one e).symm))
  · right
    apply e.injective
    have hNeg : e (-1) = -1 := by
      apply Units.ext
      change Rat.ringOfIntegersEquiv (-1) = -1
      rw [map_neg, map_one]
    exact h.trans hNeg.symm

private theorem rationalIntegralUnitToIdealSquareRadical_surjective :
    Function.Surjective (integralUnitToIdealNthPowerRadicalQuotient ℚ (2 : ℕ+)) := by
  have hClass : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    Fintype.card_le_one_iff_subsingleton.mp (le_of_eq Rat.classNumber_eq)
  intro x
  have hKer : x ∈ (idealNthPowerRadicalToClassTorsion ℚ (2 : ℕ+)).ker := by
    apply Subtype.ext
    exact hClass.elim _ _
  rw [← range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion ℚ (2 : ℕ+)] at hKer
  obtain ⟨u, hu⟩ := hKer
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective u
  exact ⟨v, hu⟩

/-- Every element of the rational ideal-square radical is zero or the
actual class of the integral unit −1. -/
theorem rationalIdealSquareRadical_eq_zero_or_neg_one
    (x : idealPowerRadicalModP ℚ 2) :
    x = 0 ∨ x = Additive.ofMul
      (integralUnitToIdealNthPowerRadicalQuotient ℚ (2 : ℕ+) (-1)) := by
  obtain ⟨u, hu⟩ := rationalIntegralUnitToIdealSquareRadical_surjective (Additive.toMul x)
  rcases rationalRingUnit_eq_one_or_neg_one u with h | h
  · left
    apply Additive.toMul.injective
    rw [h, map_one] at hu
    exact hu.symm
  · right
    apply Additive.toMul.injective
    rw [h] at hu
    exact hu.symm

end ClassFieldTower.Sawin
