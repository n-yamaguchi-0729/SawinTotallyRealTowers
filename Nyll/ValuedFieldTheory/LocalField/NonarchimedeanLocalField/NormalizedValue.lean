/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic

/-!
# Comparing normalized integer values

Every compatible surjective integer valuation gives the same integer value
on field units as the intrinsic normalized local-field valuation.
-/

@[expose] public section

noncomputable section

open scoped ValuativeRel WithZero

namespace LocalFieldTheory

universe w

private lemma withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
    (γ : WithZero (Multiplicative ℤ)) (hγ : γ < 1) :
    γ ≤ WithZero.exp (-1 : ℤ) := by
  cases γ using WithZero.recZeroCoe with
  | zero =>
      exact bot_le
  | coe γ =>
      rw [WithZero.exp_eq_coe_ofAdd, WithZero.coe_le_coe]
      rw [← Multiplicative.toAdd_le]
      change Multiplicative.toAdd γ ≤ (-1 : ℤ)
      have hγ' : Multiplicative.toAdd γ < (0 : ℤ) := by
        have : γ < (1 : Multiplicative ℤ) := by
          exact WithZero.coe_lt_coe.mp hγ
        change
          Multiplicative.toAdd γ <
            Multiplicative.toAdd (1 : Multiplicative ℤ)
        exact Multiplicative.toAdd_lt.mpr this
      omega

/-- A surjective standard integer valuation gives the same normalized
integer value as the intrinsic local-field valuation. -/
theorem normalizedValue_eq_withZeroLog_of_surjective
    (F : Type w)
    [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (ν : Valuation F (WithZero (Multiplicative ℤ)))
    [ν.Compatible]
    (hν : Function.Surjective ν)
    (x : Fˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v F
        (Additive.ofMul x) =
      WithZero.log (ν (x : F)) := by
  let ν₀ := ValuativeRel.valuation F
  have hEquiv : ν₀.IsEquiv ν :=
    ValuativeRel.isEquiv ν₀ ν
  obtain ⟨π, hπ⟩ :=
    hν (WithZero.exp (-1 : ℤ))
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let ϖ : Fˣ := Units.mk0 π hπ0
  have hπlt : ν π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hπIntrinsicLt : ν₀ π < 1 :=
    hEquiv.lt_one_iff_lt_one.mpr hπlt
  have hπIntrinsicMax :
      ∀ γ : ValuativeRel.ValueGroupWithZero F,
        γ < 1 → γ ≤ ν₀ π := by
    intro γ hγ
    obtain ⟨y, hy⟩ :=
      ValuativeRel.valuation_surjective γ
    have hylt : ν y < 1 := by
      apply hEquiv.lt_one_iff_lt_one.mp
      change ValuativeRel.valuation F y < 1
      rw [hy]
      exact hγ
    have hyle : ν y ≤ ν π := by
      rw [hπ]
      exact
        withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
          (ν y) hylt
    have hyle' : ν₀ y ≤ ν₀ π :=
      hEquiv.le_iff_le.mpr hyle
    simpa only [ν₀, hy] using hyle'
  let φ :=
    _root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hφπ :
      φ (ν₀ π) = WithZero.exp (-1 : ℤ) := by
    apply le_antisymm
    · exact
        withZeroMultiplicativeInt_le_exp_neg_one_of_lt_one
          (φ (ν₀ π)) (by
            have h := φ.strictMono hπIntrinsicLt
            simpa only [map_one] using h)
    · let γ : ValuativeRel.ValueGroupWithZero F :=
        φ.symm (WithZero.exp (-1 : ℤ))
      have hγlt : γ < 1 := by
        have hneg :
            WithZero.exp (-1 : ℤ) <
              (1 : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
          omega
        have h := φ.symm.strictMono hneg
        simpa only [map_one] using h
      have hγle := hπIntrinsicMax γ hγlt
      have hmap := φ.toOrderIso.monotone hγle
      rw [← φ.apply_symm_apply (WithZero.exp (-1 : ℤ))]
      exact hmap
  have hϖValue :
      LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul ϖ) = -1 := by
    rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_apply]
    apply (WithZero.toAdd_unzero_eq_iff _ (-1 : ℤ)).2
    change
      φ (ν₀ ((ϖ : Fˣ) : F)) =
        ((Multiplicative.ofAdd (-1 : ℤ) :
            Multiplicative ℤ) :
          WithZero (Multiplicative ℤ))
    change
      φ (ν₀ π) =
        ((Multiplicative.ofAdd (-1 : ℤ) :
            Multiplicative ℤ) :
          WithZero (Multiplicative ℤ))
    simpa only [WithZero.exp_eq_coe_ofAdd] using hφπ
  let n : ℤ := WithZero.log (ν (x : F))
  let y : Fˣ := x * ϖ ^ n
  have hxν0 : ν (x : F) ≠ 0 :=
    (Valuation.ne_zero_iff ν).2 x.ne_zero
  have hyν : ν (y : F) = 1 := by
    have hϖν : ν (ϖ : F) = WithZero.exp (-1 : ℤ) := by
      exact hπ
    calc
      ν (y : F) =
          ν (x : F) * ν (ϖ : F) ^ n := by
            simp only [y, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀]
      _ =
          WithZero.exp n * WithZero.exp (-1 : ℤ) ^ n := by
            rw [← WithZero.exp_log hxν0]
            rw [hϖν]
      _ =
          WithZero.exp n *
            WithZero.exp (n • (-1 : ℤ)) := by
              rw [WithZero.exp_zsmul]
      _ = WithZero.exp (n + n • (-1 : ℤ)) := by
            rw [WithZero.exp_add]
      _ = 1 := by
            rw [zsmul_eq_mul, Int.cast_id, mul_neg, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hyInvν : ν ((y⁻¹ : Fˣ) : F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hyν, inv_one]
  have hyMem : (y : F) ∈ 𝒪[F] := by
    change ν₀ (y : F) ≤ 1
    exact hEquiv.le_one_iff_le_one.mpr (by rw [hyν])
  have hyInvMem : ((y⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    change ν₀ ((y⁻¹ : Fˣ) : F) ≤ 1
    exact hEquiv.le_one_iff_le_one.mpr (by rw [hyInvν])
  let yInteger : 𝒪[F]ˣ :=
    { val := ⟨(y : F), hyMem⟩
      inv := ⟨((y⁻¹ : Fˣ) : F), hyInvMem⟩
      val_inv := Subtype.ext y.val_inv
      inv_val := Subtype.ext y.inv_val }
  have hyField :
      LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
          F yInteger =
        y := by
    apply Units.ext
    rfl
  have hyValue :
      LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul y) = 0 := by
    rw [← hyField]
    exact
      LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
        F yInteger
  have hdecomp : y * ϖ ^ (-n) = x := by
    rw [show y = x * ϖ ^ n by rfl, mul_assoc, zpow_neg,
      mul_inv_cancel, mul_one]
  have hdecompValue :=
    congrArg
      (fun z : Fˣ =>
        LocalFieldTheory.IsNonarchimedeanLocalField.v F
          (Additive.ofMul z))
      hdecomp
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_mul,
    hyValue,
    LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow,
    hϖValue] at hdecompValue
  dsimp [n] at hdecompValue ⊢
  linarith

end LocalFieldTheory
