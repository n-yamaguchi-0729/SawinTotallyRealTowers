/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# A height-two localization detected by a nonunit integer

Let `t` generate a prime divisor in a Noetherian local domain.  If a positive
integer `e` is nonzero but noninvertible modulo `t`, then a minimal prime over
`(t, e)` has height exactly two.  At that prime, `e` remains a nonunit.

This is the codimension-two reduction used in the local-purity part of the
one-point inertia argument.  Its hypotheses are only the source-side divisor
and residue-characteristic data; no height-two prime is supplied as input.
-/

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A positive nonunit integer modulo a prime parameter produces a
height-two prime at which that integer is still a nonunit. -/
theorem exists_heightTwo_prime_of_nonunit_natCast_mod_prime
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A]
    (t : A) (ht : Prime t) (e : ℕ) (he : 0 < e)
    [CharZero (A ⧸ Ideal.span {t})]
    (he_nonunit : ¬ IsUnit (e : A ⧸ Ideal.span {t})) :
    ∃ (P : Ideal A) (_ : P.IsPrime),
      P ∈ (Ideal.span {t, (e : A)}).minimalPrimes ∧
      Ideal.span {t} < P ∧
      P.height = 2 ∧
      ¬ IsUnit
        (algebraMap A (Localization.AtPrime P) (e : A)) := by
  classical
  have he_notmem : (e : A) ∉ Ideal.span {t} := by
    intro he_mem
    have he_zero : (e : A ⧸ Ideal.span {t}) = 0 := by
      simpa using Ideal.Quotient.eq_zero_iff_mem.mpr he_mem
    exact (Nat.cast_ne_zero.mpr he.ne') he_zero
  have he_nonunit_A : ¬ IsUnit (e : A) := by
    intro he_unit
    exact he_nonunit (he_unit.map (Ideal.Quotient.mk (Ideal.span {t})))
  have hpair_le : Ideal.span {t, (e : A)} ≤ maximalIdeal A := by
    rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with hxt | hxe
    · subst x
      exact (mem_maximalIdeal t).mpr (mem_nonunits_iff.mpr ht.not_isUnit)
    · subst x
      exact (mem_maximalIdeal (e : A)).mpr (mem_nonunits_iff.mpr he_nonunit_A)
  obtain ⟨P, hPmin, -⟩ :=
    Ideal.exists_minimalPrimes_le hpair_le
  let : P.IsPrime := hPmin.isPrime
  let : (Ideal.span {t}).IsPrime :=
    Ideal.isPrime_span_singleton_of_prime ht
  have htP : t ∈ P := hPmin.le (Ideal.subset_span (by simp))
  have heP : (e : A) ∈ P := hPmin.le (Ideal.subset_span (by simp))
  have hspan_le : Ideal.span {t} ≤ P := Ideal.span_le.mpr (by simpa)
  have hspan_lt : Ideal.span {t} < P :=
    hspan_le.lt_of_not_ge fun hPspan ↦ he_notmem (hPspan heP)
  have hspan_height : (Ideal.span {t}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr ht.ne_zero) ht.not_isUnit
  have hheight_lower : (2 : ℕ∞) ≤ P.height := by
    have := Ideal.height_add_one_le_of_lt_of_isPrime hspan_lt
    simpa only [hspan_height, one_add_one_eq_two] using this
  have hte : t ≠ (e : A) := by
    intro hte
    apply he_notmem
    rw [← hte]
    exact Ideal.mem_span_singleton_self t
  have hheight_upper : P.height ≤ (2 : ℕ∞) := by
    have h := Ideal.height_le_ncard_of_mem_minimalPrimes_span
      (s := {t, (e : A)}) (Set.toFinite _) hPmin
    simpa [hte] using h
  have hheight : P.height = 2 := le_antisymm hheight_upper hheight_lower
  have he_local_nonunit :
      ¬ IsUnit (algebraMap A (Localization.AtPrime P) (e : A)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P]
    simpa only [Ideal.mem_primeCompl_iff, not_not] using heP
  exact ⟨P, inferInstance, hPmin, hspan_lt, hheight, he_local_nonunit⟩

end EtaleFundamentalGroups
