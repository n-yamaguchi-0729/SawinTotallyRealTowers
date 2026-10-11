/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A DVR fraction field is a principal localization

Every nonzero denominator divides a power of any fixed nonzero nonunit:
a uniformizer divides that nonunit, while each denominator is associated
to a power of the uniformizer. Thus localization at that nonunit already
inverts all nonzero elements.
-/

namespace SchemeTheory

open scoped nonZeroDivisors

universe u v

/-- Inverting a nonzero nonunit of a discrete valuation ring gives its
actual fraction field, with its existing algebra map. -/
theorem isLocalizationAway_fractionField_of_isDiscreteValuationRing
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (a : R) (ha0 : a ≠ 0) (ha : ¬ IsUnit a) :
    IsLocalization.Away a K := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπa : π ∣ a := by
    apply Ideal.mem_span_singleton.mp
    rw [← hπ.maximalIdeal_eq]
    exact ha
  have hcofinal : ∀ b ∈ nonZeroDivisors R,
      ∃ c ∈ Submonoid.powers a, b ∣ c := by
    intro b hb
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mem_nonZeroDivisors_iff_ne_zero.mp hb) hπ
    exact ⟨a ^ n, ⟨n, rfl⟩, hn.dvd.trans (pow_dvd_pow_of_dvd hπa n)⟩
  exact (IsLocalization.iff_of_le_of_exists_dvd (S := K)
    (Submonoid.powers a) (nonZeroDivisors R)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ha0) hcofinal).mpr inferInstance

end SchemeTheory
