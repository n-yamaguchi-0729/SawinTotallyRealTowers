/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicMuPKummerComparison
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
import Mathlib.GroupTheory.ArchimedeanDensely
import Mathlib.RingTheory.Valuation.Discrete.RankOne

set_option autoImplicit false
/-!
# Compatibility of finite-place normalized valuations with the diagonal

The intrinsic local normalization agrees with the distinguished integer-valued adic
valuation: the only order-preserving automorphism of the integer value group is the identity.
Consequently localization of global power classes preserves their finite-valuation defects.

The two completion structures are local instances shared by the three public lemmas. Only
compatibility of the distinguished valuation is introduced inside a proof; no new global
instance or additional arithmetic hypothesis is needed.
-/

open scoped NumberField ValuativeRel WithZero

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

private theorem orderMonoidIso_withZeroInt_apply
    (e : ℤᵐ⁰ ≃*o ℤᵐ⁰) (x : ℤᵐ⁰) : e x = x := by
  let eu : Multiplicative ℤ ≃* Multiplicative ℤ :=
    WithZero.unitsWithZeroEquiv.symm.trans
      ((Units.mapEquiv e.toMulEquiv).trans WithZero.unitsWithZeroEquiv)
  have heu (a : Multiplicative ℤ) : (eu a : ℤᵐ⁰) = e (a : ℤᵐ⁰) := by
    simp [eu]
  let ez : ℤ ≃+o ℤ :=
    { __ := eu.toAdditive
      map_le_map_iff' := by
        intro a b
        change eu (Multiplicative.ofAdd a) ≤ eu (Multiplicative.ofAdd b) ↔ a ≤ b
        rw [← WithZero.coe_le_coe, heu, heu, map_le_map_iff]
        exact WithZero.coe_le_coe }
  have hez : ez = OrderAddMonoidIso.refl ℤ := Subsingleton.elim _ _
  rcases eq_or_ne x 0 with rfl | hx
  · exact map_zero e
  · lift x to Multiplicative ℤ using hx
    have h := congrArg (fun f : ℤ ≃+o ℤ => f x.toAdd) hez
    change (eu x).toAdd = x.toAdd at h
    have hx : eu x = x := Multiplicative.toAdd.injective h
    rw [← heu x, hx]

private theorem localIntegerValuation_eq_of_surjective
    (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    (ν : Valuation L ℤᵐ⁰) [ν.Compatible] [ν.IsRankOneDiscrete]
    (hν : Function.Surjective ν) : LocalFieldTheory.localIntegerValuation L = ν := by
  let e : ValuativeRel.ValueGroupWithZero L ≃*o ℤᵐ⁰ :=
    (ValuativeRel.ValueGroupWithZero.orderMonoidIso ν).trans
      (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν)
  have he : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L = e := by
    ext a
    have h := orderMonoidIso_withZeroInt_apply
      ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).symm.trans e)
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L a)
    simpa only [OrderMonoidIso.trans_apply, OrderMonoidIso.symm_apply_apply] using h.symm
  ext x
  rw [LocalFieldTheory.localIntegerValuation_apply, he]
  change Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt ν
    ((ValuativeRel.ValueGroupWithZero.orderMonoidIso ν)
      (ValuativeRel.valuation L x)) = ν x
  rw [ValuativeRel.ValueGroupWithZero.orderMonoidIso_valuation_eq_restrict₀]
  exact Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
    hν x

open IsDedekindDomain KummerTheory

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]
variable (v : HeightOneSpectrum (𝓞 K))

local instance : ValuativeRel (v.adicCompletion K) :=
  finitePlaceAdicCompletionValuativeRel K v

local instance : IsNonarchimedeanLocalField (v.adicCompletion K) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField K v

/-- Intrinsic local normalization is the distinguished adic valuation. -/
theorem finitePlaceLocalIntegerValuation_eq :
    LocalFieldTheory.localIntegerValuation (v.adicCompletion K) =
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) := by
  let ν : Valuation (v.adicCompletion K) ℤᵐ⁰ := Valued.v
  let : ν.Compatible := Valuation.Compatible.ofValuation ν
  exact localIntegerValuation_eq_of_surjective (v.adicCompletion K) ν
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v)

/-- The normalized valuation of a diagonal unit equals its global finite-place valuation. -/
theorem finitePlaceValuationMap_diagonal (a : Kˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap (v.adicCompletion K)
        (Additive.ofMul (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)) =
      (v.valuationOfNeZero a).toAdd := by
  apply WithZero.exp_injective
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap_apply,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_apply]
  simp only [WithZero.exp, ofAdd_toAdd, WithZero.coe_unzero]
  change LocalFieldTheory.localIntegerValuation (v.adicCompletion K)
    (algebraMap K (v.adicCompletion K) (a : K)) =
      (v.valuationOfNeZero a : ℤᵐ⁰)
  rw [finitePlaceLocalIntegerValuation_eq, HeightOneSpectrum.valuationOfNeZero_eq]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (a : K)

/-- Localization preserves the mod-`p` finite-valuation defect of every global power class. -/
theorem finitePlaceLocalPowerClassValuation_localization
    (x : absolutePowerClassModP K p) :
    finitePlaceLocalPowerClassValuation K p v
        (finitePlacePowerClassLocalization K p v x) =
      (v.valuationOfNeZeroMod p (Additive.toMul x)).toAdd := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom p : Kˣ →* Kˣ).range (Additive.toMul x)
  have hx : x = Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a) :=
    Additive.toMul.injective ha.symm
  rw [hx]
  change (LocalClassFieldTheory.valuationModDegreeMulHom (v.adicCompletion K) p
      (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)).toAdd = _
  rw [LocalClassFieldTheory.valuationModDegreeMulHom_apply]
  change (LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap (v.adicCompletion K)
      (Additive.ofMul (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)) :
        ZMod p) = _
  rw [finitePlaceValuationMap_diagonal]
  rfl

end ClassFieldTower.Martinet.Shafarevich
