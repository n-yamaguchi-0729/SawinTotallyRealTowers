/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Actual principal-unit multipliers and field-unit quotients

The intrinsic ring predicate used by the DVR character kernel is equivalent
to the field-unit predicate used by Hilbert ramification. The proof constructs
the required units and uses the valuation alternative, without any fraction
field scalar dictionaries or a supplied subgroup comparison.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u

private theorem mem_principalUnitGroup_iff_exists_principal_unit
    {L : Type u} [Field L] (V : _root_.ValuationSubring L) (q : Lˣ) :
    q ∈ V.principalUnitGroup ↔
      ∃ a : Vˣ, ((a : V) : L) = (q : L) ∧
        (a : V) - 1 ∈ IsLocalRing.maximalIdeal V := by
  constructor
  · intro hq
    let aq : V.unitGroup := ⟨q, V.principal_units_le_units hq⟩
    refine ⟨V.unitGroupMulEquiv aq, V.coe_unitGroupMulEquiv_apply aq, ?_⟩
    apply (V.valuation_lt_one_iff ((V.unitGroupMulEquiv aq : V) - 1)).mpr
    change V.valuation (((V.unitGroupMulEquiv aq : V) : L) - 1) < 1
    rw [V.coe_unitGroupMulEquiv_apply aq]
    exact (V.mem_principalUnitGroup_iff q).mp hq
  · rintro ⟨a, ha, hprincipal⟩
    apply (V.mem_principalUnitGroup_iff q).mpr
    have hval := (V.valuation_lt_one_iff ((a : V) - 1)).mp hprincipal
    change V.valuation (((a : V) : L) - 1) < 1 at hval
    rwa [ha] at hval

/-- A compatible actual field endomorphism acts by principal-unit
multipliers on every valuation-ring element exactly when all its field-unit
quotients are principal units. -/
theorem principalUnitMultipliers_iff_unitQuotients
    {L : Type u} [Field L] (V : _root_.ValuationSubring L)
    (σ : L →+* L) (τ : V →+* V)
    (hcompat : V.subtype.comp τ = σ.comp V.subtype) :
    (∀ x : V, ∃ a : Vˣ,
      τ x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) ↔
      ∀ x : Lˣ, Units.map σ.toMonoidHom x / x ∈ V.principalUnitGroup := by
  constructor
  · intro h
    have hsmall (x : Lˣ) (hx : (x : L) ∈ V) :
        Units.map σ.toMonoidHom x / x ∈ V.principalUnitGroup := by
      obtain ⟨a, ha, hres⟩ := h ⟨x, hx⟩
      have haL : σ (x : L) = (x : L) * ((a : V) : L) :=
        (RingHom.congr_fun hcompat ⟨x, hx⟩).symm.trans (congrArg (fun z : V => (z : L)) ha)
      apply (mem_principalUnitGroup_iff_exists_principal_unit V _).mpr
      refine ⟨a, ?_, hres⟩
      rw [Units.val_div_eq_div_val, Units.coe_map]
      change ((a : V) : L) = σ (x : L) / (x : L)
      apply (eq_div_iff (Units.ne_zero x)).mpr
      exact (mul_comm _ _).trans haL.symm
    intro x
    rcases V.mem_or_inv_mem (x : L) with hx | hx
    · exact hsmall x hx
    · have hx' : ((x⁻¹ : Lˣ) : L) ∈ V := by
        rw [Units.val_inv_eq_inv_val]
        exact hx
      have h := hsmall x⁻¹ hx'
      have heq : Units.map σ.toMonoidHom x⁻¹ / x⁻¹ =
          (Units.map σ.toMonoidHom x / x)⁻¹ := by
        rw [map_inv, inv_div, div_inv_eq_mul, div_eq_mul_inv, mul_comm]
      rw [heq] at h
      exact V.principalUnitGroup.inv_mem_iff.mp h
  · intro h x
    by_cases hx : x = 0
    · subst x
      refine ⟨1, ?_, ?_⟩
      · rw [map_zero, zero_mul]
      · change (1 : V) - 1 ∈ IsLocalRing.maximalIdeal V
        rw [sub_self]
        exact (IsLocalRing.maximalIdeal V).zero_mem
    · have hxL : (x : L) ≠ 0 := fun hzero => hx (Subtype.ext hzero)
      let xL : Lˣ := Units.mk0 (x : L) hxL
      obtain ⟨a, ha, hres⟩ :=
        (mem_principalUnitGroup_iff_exists_principal_unit V _).mp (h xL)
      refine ⟨a, ?_, hres⟩
      apply Subtype.ext
      change (τ x : L) = (x : L) * ((a : V) : L)
      have hc : (τ x : L) = σ (x : L) := RingHom.congr_fun hcompat x
      rw [hc, ha]
      rw [Units.val_div_eq_div_val, Units.coe_map]
      change σ (x : L) = (x : L) * (σ (x : L) / (x : L))
      rw [mul_comm, div_mul_cancel₀ _ hxL]

end RamificationTheory.HilbertRamification.DiscreteValuationRing
