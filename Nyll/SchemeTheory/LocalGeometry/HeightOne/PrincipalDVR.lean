/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# A Noetherian-free DVR criterion in dimension one

A local domain of Krull dimension at most one whose nonzero maximal ideal
is principal is a discrete valuation ring.  The usual DVR TFAE in mathlib
assumes Noetherianity.  Here Noetherianity is a conclusion rather than an
input: the unique nonzero-prime geometry forces every nonzero element to be
a unit times a power of a generator of the maximal ideal.

This form is intended for local rings cut out inside an adic base change,
where a global `IsNoetherianRing` instance on the completion is not
available.  A retained generic component supplies the dimension bound, and
the exact vertical-fibre calculation supplies the principal maximal ideal.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A one-dimensional local domain with nonzero principal maximal ideal is
a DVR, without a Noetherian hypothesis.

The proof first obtains a prime generator `varpi` of the maximal ideal.
Every minimal prime above `(x)` for `x != 0` is a nonzero prime, hence the
unique maximal ideal by `KrullDimLE 1`.  Thus a power of `varpi` belongs to
`(x)`.  Cancelling one `varpi` at a time gives the required unit-times-power
factorization, from which mathlib constructs the local PID. -/
theorem isDiscreteValuationRing_of_krullDimLE_one_of_maximalIdeal_isPrincipal
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [Ring.KrullDimLE 1 A]
    (hnotField : ¬ IsField A)
    (hprincipal : (IsLocalRing.maximalIdeal A).IsPrincipal) :
    IsDiscreteValuationRing A := by
  classical
  obtain ⟨varpi, hvarpiSpan⟩ := hprincipal
  have hmaxNe : IsLocalRing.maximalIdeal A ≠ ⊥ :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnotField
  have hvarpiNe : varpi ≠ 0 := by
    intro hzero
    apply hmaxNe
    rw [hvarpiSpan, hzero, Set.singleton_zero,
      Submodule.span_zero]
  have hvarpiIrreducible : Irreducible varpi :=
    IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      varpi hvarpiNe hvarpiSpan
  have power_associated_of_power_mem_span :
      ∀ {x : A}, x ≠ 0 → ∀ n : ℕ,
        varpi ^ n ∈ Ideal.span ({x} : Set A) →
          ∃ k : ℕ, Associated (varpi ^ k) x := by
    intro x hx n
    induction n generalizing x with
    | zero =>
        intro hmem
        have hxUnit : IsUnit x := by
          rw [pow_zero, Ideal.mem_span_singleton] at hmem
          exact isUnit_iff_dvd_one.mpr hmem
        exact ⟨0, by
          simpa using (associated_one_iff_isUnit.mpr hxUnit).symm⟩
    | succ n ih =>
        intro hmem
        by_cases hxUnit : IsUnit x
        · exact ⟨0, by
            simpa using (associated_one_iff_isUnit.mpr hxUnit).symm⟩
        have hxMax : x ∈ IsLocalRing.maximalIdeal A :=
          (IsLocalRing.mem_maximalIdeal x).mpr hxUnit
        have hvarpiDvd : varpi ∣ x := by
          rw [hvarpiSpan, Ideal.mem_span_singleton] at hxMax
          exact hxMax
        obtain ⟨x', rfl⟩ := hvarpiDvd
        have hx'Ne : x' ≠ 0 := by
          intro hx'Zero
          apply hx
          rw [hx'Zero, mul_zero]
        have hsmaller :
            varpi ^ n ∈ Ideal.span ({x'} : Set A) := by
          rw [Ideal.mem_span_singleton] at hmem ⊢
          obtain ⟨c, hc⟩ := hmem
          refine ⟨c, ?_⟩
          apply mul_left_cancel₀ hvarpiNe
          calc
            varpi * varpi ^ n = varpi ^ (n + 1) := by
              rw [pow_succ']
            _ = (varpi * x') * c := hc
            _ = varpi * (x' * c) := by ac_rfl
        obtain ⟨k, hk⟩ := ih hx'Ne hsmaller
        exact ⟨k + 1, by
          simpa [pow_succ'] using hk.mul_left varpi⟩
  apply IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
  refine ⟨varpi, hvarpiIrreducible, ?_⟩
  intro x hx
  have hvarpiRadical :
      varpi ∈ (Ideal.span ({x} : Set A)).radical := by
    rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro P hP
    have hxP : x ∈ P :=
      hP.le (Ideal.mem_span_singleton.mpr (dvd_refl x))
    have hPNe : P ≠ ⊥ := by
      intro hPBot
      have : x = 0 := by
        rw [hPBot, Ideal.mem_bot] at hxP
        exact hxP
      exact hx this
    have hPMax : P.IsMaximal :=
      hP.isPrime.isMaximal_of_ne_bot hPNe
    have hPEq : P = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal hPMax
    rw [hPEq, hvarpiSpan]
    exact Ideal.mem_span_singleton.mpr (dvd_refl varpi)
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hvarpiRadical
  exact power_associated_of_power_mem_span hx n hn

end EtaleFundamentalGroups

end
