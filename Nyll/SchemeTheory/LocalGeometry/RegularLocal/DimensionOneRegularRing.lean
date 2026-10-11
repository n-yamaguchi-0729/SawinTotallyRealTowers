/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# One-dimensional regular local domains are regular rings

In dimension one every nonzero prime of a local domain is maximal.  Thus a
one-dimensional regular local domain is regular at all of its primes without
using the missing general theorem that arbitrary regular local rings are
regular rings.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A one-dimensional regular local domain is a regular ring. -/
theorem isRegularRing_of_isRegularLocalRing_dimension_one
    {R : Type u} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = ((1 : ℕ∞) : WithBot ℕ∞)) :
    IsRegularRing R := by
  rw [isRegularRing_iff]
  intro p hp
  by_cases hpBot : p = ⊥
  · subst p
    let : Field (Localization.AtPrime (⊥ : Ideal R)) :=
      IsField.toField (by
        simp [isField_iff_maximalIdeal_eq,
          ← Localization.AtPrime.map_eq_maximalIdeal])
    infer_instance
  · have hpLe : p ≤ IsLocalRing.maximalIdeal R :=
      IsLocalRing.le_maximalIdeal_of_isPrime p
    have hMaxHeight :
        (IsLocalRing.maximalIdeal R).height = (1 : ℕ∞) := by
      have hMaxHeightCast :
          (((IsLocalRing.maximalIdeal R).height : ℕ∞) : WithBot ℕ∞) =
            ((1 : ℕ∞) : WithBot ℕ∞) := by
        rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdim]
      exact WithBot.coe_eq_coe.mp hMaxHeightCast
    have hpHeightPos : (1 : ℕ∞) ≤ p.height :=
      Order.one_le_iff_ne_zero.mpr
        (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpBot)
    have hpHeightLe : p.height ≤ (1 : ℕ∞) := by
      rw [← hMaxHeight]
      exact Ideal.height_mono hpLe
    have hpHeight : p.height = (1 : ℕ∞) :=
      le_antisymm hpHeightLe hpHeightPos
    have hpMax : p = IsLocalRing.maximalIdeal R := by
      by_contra hpNe
      have hpLt : p < IsLocalRing.maximalIdeal R := lt_of_le_of_ne hpLe hpNe
      have := Ideal.height_strict_mono_of_isPrime_of_isPrime hpLt
      rw [hpHeight, hMaxHeight] at this
      exact (lt_irrefl (1 : ℕ∞)) this
    subst p
    let e : R ≃ₐ[R]
        Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
      IsLocalization.atUnits R
        (IsLocalRing.maximalIdeal R).primeCompl
        (fun x ↦ by simpa using! fun a ↦ a)
    exact IsRegularLocalRing.of_ringEquiv e.toRingEquiv

end EtaleFundamentalGroups

end
