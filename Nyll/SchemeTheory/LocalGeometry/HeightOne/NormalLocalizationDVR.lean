/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.Submodule

/-!
# Height-one localizations of Noetherian normal domains

A height-one localization of a Noetherian integrally closed domain is a
one-dimensional normal Noetherian local domain, hence a DVR.  This is the
form needed for height-one primes in finite normalizations; no regularity of
the unlocalized normalization is required.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A height-one localization of a Noetherian normal domain is a DVR. -/
theorem
    isDiscreteValuationRing_localizationAtPrime_of_normal_noetherian_height_one
    {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    [IsIntegrallyClosed S]
    (q : Ideal S) [q.IsPrime] (hqHeight : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  let V := Localization.AtPrime q
  let : IsNoetherianRing V :=
    IsLocalization.isNoetherianRing q.primeCompl V inferInstance
  let : IsIntegrallyClosed V :=
    isIntegrallyClosed_of_isLocalization
      V q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hqNe : q ≠ ⊥ := by
    intro hq
    have hzero : q.height = 0 := Ideal.height_eq_zero_iff_eq_bot.mpr hq
    rw [hqHeight] at hzero
    norm_num at hzero
  have hnotField : ¬ IsField V :=
    IsLocalization.AtPrime.not_isField S hqNe V
  have hdimV : ringKrullDim V = ((1 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim V = (q.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height q V
      _ = ((1 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hqHeight
  have hkrullDimLE : Ring.KrullDimLE 1 V := by
    rw [Ring.krullDimLE_iff, hdimV]
    exact le_rfl
  have hmaximalOfNonzeroPrime :
      ∀ (P : Ideal V), P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_isPrime_bot.mp hkrullDimLE
  have huniqueNonzeroPrime :
      ∃! P : Ideal V, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal V, ?_, ?_⟩
    · exact ⟨isField_iff_maximalIdeal_eq.not.mp hnotField, inferInstance⟩
    · intro P hP
      exact IsLocalRing.eq_maximalIdeal
        (hmaximalOfNonzeroPrime P hP.1 hP.2)
  have hnormalUnique :
      IsIntegrallyClosed V ∧
        ∃! P : Ideal V, P ≠ ⊥ ∧ P.IsPrime :=
    ⟨inferInstance, huniqueNonzeroPrime⟩
  exact ((IsDiscreteValuationRing.TFAE V hnotField).out 1 4).mpr
    hnormalUnique

end EtaleFundamentalGroups

end
