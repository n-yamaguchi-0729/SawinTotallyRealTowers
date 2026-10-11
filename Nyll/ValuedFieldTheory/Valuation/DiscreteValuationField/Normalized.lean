/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Integer-valued normalization of a discrete valuation

The maximal ideal of the actual valuation ring supplies an integer-valued
discrete valuation on its fraction field. Its valuation subring is the
original subring of that same field, without a Henselianity assumption.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v

/-- Normalize a discrete valuation together with an element of value exp(-1). -/
theorem exists_normalized_valuation_with_uniformizer
    {K : Type u} [Field K] (base : DVF.{u, v} K) :
    ∃ w : _root_.Valuation K (WithZero (Multiplicative ℤ)),
      w.IsRankOneDiscrete ∧ w.valuationSubring = base.valuation.valuationSubring ∧
        ∃ π : K, w π = WithZero.exp (-1 : ℤ) := by
  have : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  have : IsFractionRing base.valuationSubring K := base.valuationSubring_isFractionRing
  let w : _root_.Valuation K (WithZero (Multiplicative ℤ)) :=
    (IsDiscreteValuationRing.maximalIdeal base.valuationSubring).valuation K
  refine ⟨w, IsDiscreteValuationRing.isRankOneDiscrete base.valuationSubring K, ?_, ?_⟩
  swap
  · exact IsDedekindDomain.HeightOneSpectrum.valuation_exists_uniformizer K
      (IsDiscreteValuationRing.maximalIdeal base.valuationSubring)
  have hmap : Subring.map (algebraMap base.valuationSubring K) ⊤ =
      w.valuationSubring.toSubring :=
    IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := base.valuationSubring) (K := K)
  apply SetLike.ext
  intro x
  change x ∈ w.valuationSubring.toSubring ↔ x ∈ base.valuation.valuationSubring
  rw [← hmap]
  constructor
  · intro hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact y.property
  · intro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩


/-- Every discrete valuation can be normalized to integer values while
retaining exactly the same valuation subring in the original field. -/
theorem exists_normalized_valuation
    {K : Type u} [Field K] (base : DVF.{u, v} K) :
    ∃ w : _root_.Valuation K (WithZero (Multiplicative ℤ)),
      w.IsRankOneDiscrete ∧ w.valuationSubring = base.valuation.valuationSubring := by
  obtain ⟨w, hw, hring, _⟩ := base.exists_normalized_valuation_with_uniformizer
  exact ⟨w, hw, hring⟩

end ValuationTheory.DiscreteValuationField.DVF
