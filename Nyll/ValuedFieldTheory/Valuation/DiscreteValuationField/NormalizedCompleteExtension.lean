/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Uniqueness

/-!
# Integer-valued complete extensions

The integral closure supplies a complete extension valuation, and its
localization supplies an integer-valued discrete extension valuation.
Uniqueness identifies their valuation subrings and transports completeness.
-/

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w

private theorem isCompleteDiscrete_of_valuationSubring_eq
    {L Γ₁ Γ₂ : Type*} [Field L]
    [LinearOrderedCommGroupWithZero Γ₁] [LinearOrderedCommGroupWithZero Γ₂]
    (v₁ : _root_.Valuation L Γ₁) (v₂ : _root_.Valuation L Γ₂)
    [Valuation.IsCompleteDiscrete v₁] [v₂.IsRankOneDiscrete]
    (h : v₁.valuationSubring = v₂.valuationSubring) :
    Valuation.IsCompleteDiscrete v₂ := by
  refine { isRankOneDiscrete := inferInstance, isAdicComplete := ?_ }
  let P : ValuationSubring L → Prop := fun V =>
    IsAdicComplete (IsLocalRing.maximalIdeal V) V
  have hcomplete : P v₁.valuationSubring := Valuation.isAdicComplete v₁
  exact h ▸ hcomplete

/-- Every finite separable extension of a complete DVF has an actual
integer-valued complete discrete valuation extending the base valuation. -/
theorem exists_normalized_complete_valuation_of_finite_separable
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (base : CompleteDVF.{u, v} K) :
    ∃ vL : _root_.Valuation L (WithZero (Multiplicative ℤ)),
      Valuation.IsCompleteDiscrete vL ∧ base.valuation.HasExtension vL := by
  obtain ⟨target, htarget, _⟩ :=
    exists_integralClosure_standard_fundamental_identity (L := L) base
  let : base.valuation.HasExtension target.valuation := htarget
  let normalized := FiniteExtensionLocalization.dvf (L := L) base.toDVF
  have : base.valuation.HasExtension normalized.valuation :=
    FiniteExtensionLocalization.dvf_hasExtension (L := L) base.toDVF
  have hequiv : target.valuation.IsEquiv normalized.valuation :=
    hasUniqueValuationExtension_of_finite_separable base target normalized.valuation
  have hsubring : target.valuation.valuationSubring =
      normalized.valuation.valuationSubring :=
    (_root_.Valuation.isEquiv_iff_valuationSubring
      target.valuation normalized.valuation).mp hequiv
  exact ⟨normalized.valuation,
    isCompleteDiscrete_of_valuationSubring_eq target.valuation normalized.valuation hsubring,
    this⟩

end ValuationTheory.DiscreteValuationField.ValuedExtension
