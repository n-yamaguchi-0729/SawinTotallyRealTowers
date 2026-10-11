/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.PuncturedHypersurfacePrime
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.Push

/-!
# Height-one primes containing an element of a local ring

This file proves the local-ring prime-existence statement of Stacks Project
Tag 0BJG. A prime chain selects a positive-dimensional component of a
hypersurface, and localization decreases the positive height.
-/

open IsLocalRing

namespace SchemeTheory

universe u

private theorem two_le_quotient_dimension_of_prime_chain
    {R : Type u} [CommRing R] [IsLocalRing R]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hPQ : P < Q) (hQm : Q < maximalIdeal R) :
    (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) := by
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  have : IsLocalRing (R ⧸ P) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hker : RingHom.ker q ≤ Q := by
    rw [Ideal.mk_ker]
    exact hPQ.le
  let Q' := Q.map q
  have : Q'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : Q'.comap q = Q := by
    rw [Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hPQ.le]
  have hQ'bot : (⊥ : Ideal (R ⧸ P)) < Q' := by
    apply lt_of_le_of_ne bot_le
    intro h
    have hQP : Q = P := by
      rw [← hcomap, ← h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact hPQ.ne hQP.symm
  have hQ'm : Q' < maximalIdeal (R ⧸ P) := by
    apply lt_of_le_of_ne (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
    intro h
    have hQm' : Q = maximalIdeal R := by
      rw [← hcomap, h, maximalIdeal_comap q]
    exact hQm.ne hQm'
  have hOne : (1 : ℕ∞) ≤ Q'.height := by
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hQ'bot
    exact (le_add_self : (1 : ℕ∞) ≤ (⊥ : Ideal (R ⧸ P)).height + 1).trans h
  have hTwo : (2 : ℕ∞) ≤ (maximalIdeal (R ⧸ P)).height := by
    calc
      (2 : ℕ∞) = 1 + 1 := rfl
      _ ≤ Q'.height + 1 := add_le_add hOne le_rfl
      _ ≤ (maximalIdeal (R ⧸ P)).height := Ideal.height_add_one_le_of_lt_of_isPrime hQ'm
  rw [← maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr hTwo

private theorem exists_positive_height_prime_below_maximal
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R)
    (f : R) (hf : f ∈ maximalIdeal R) :
    ∃ Q : Ideal R, Q.IsPrime ∧ f ∈ Q ∧
      (1 : ℕ∞) ≤ Q.height ∧ Q < maximalIdeal R := by
  classical
  have hmax : ¬ (maximalIdeal R).height ≤ (1 : ℕ) := by
    intro h
    have hbound : (2 : WithBot ℕ∞) ≤ 1 := by
      apply hdim.trans
      rw [← maximalIdeal_height_eq_ringKrullDim]
      exact WithBot.coe_le_coe.mpr h
    norm_num at hbound
  rw [Ideal.height_le_iff] at hmax
  push Not at hmax
  obtain ⟨Q, hQ, hQm, hQheight⟩ := hmax
  have : Q.IsPrime := hQ
  have hQzero : ¬ Q.height ≤ (0 : ℕ) := by
    exact not_le_of_gt (lt_of_lt_of_le zero_lt_one hQheight)
  rw [Ideal.height_le_iff] at hQzero
  push Not at hQzero
  obtain ⟨P, hP, hPQ, _⟩ := hQzero
  have : P.IsPrime := hP
  have hQuot := two_le_quotient_dimension_of_prime_chain P Q hPQ hQm
  obtain ⟨x, hxQ, hxP⟩ := IsConcreteLE.exists_of_lt hPQ
  by_cases hfP : f ∈ P
  · obtain ⟨Q', hQ', hPQ', hxQ', hQ'm⟩ :=
      exists_prime_over_containing_ne_maximal_of_two_le_quotient_ringKrullDim R P hQuot
        x (hQm.le hxQ)
    have : Q'.IsPrime := hQ'
    have hPQ'lt : P < Q' := lt_of_le_of_ne hPQ' (fun h => hxP (h.symm ▸ hxQ'))
    have hOne := Ideal.height_add_one_le_of_lt_of_isPrime hPQ'lt
    exact ⟨Q', hQ', hPQ' hfP,
      (le_add_self : (1 : ℕ∞) ≤ P.height + 1).trans hOne,
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ'.ne_top) hQ'm⟩
  · obtain ⟨Q', hQ', hPQ', hfQ', hQ'm⟩ :=
      exists_prime_over_containing_ne_maximal_of_two_le_quotient_ringKrullDim R P hQuot f hf
    have : Q'.IsPrime := hQ'
    have hPQ'lt : P < Q' := lt_of_le_of_ne hPQ' (fun h => hfP (h.symm ▸ hfQ'))
    have hOne := Ideal.height_add_one_le_of_lt_of_isPrime hPQ'lt
    exact ⟨Q', hQ', hfQ',
      (le_add_self : (1 : ℕ∞) ≤ P.height + 1).trans hOne,
      lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ'.ne_top) hQ'm⟩

/-- Every element of the maximal ideal of a positive-dimensional Noetherian
local ring lies in a height-one prime. -/
theorem exists_height_one_prime_containing
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (f : R) (hf : f ∈ maximalIdeal R) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P.height = 1 := by
  classical
  have hmax : (1 : ℕ∞) ≤ (maximalIdeal R).height := by
    apply WithBot.coe_le_coe.mp
    rw [maximalIdeal_height_eq_ringKrullDim]
    exact hdim
  have hex : ∃ n : ℕ, ∃ P : Ideal R,
      P.IsPrime ∧ f ∈ P ∧ P.height = n ∧ 1 ≤ n := by
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
      (Ideal.height_ne_top_of_isPrime (I := maximalIdeal R))
    refine ⟨n, maximalIdeal R, inferInstance, hf, hn.symm, ?_⟩
    rw [← hn] at hmax
    exact_mod_cast hmax
  let n := Nat.find hex
  obtain ⟨P, hP, hfP, hheight, hn⟩ := Nat.find_spec hex
  have : P.IsPrime := hP
  have hnOne : n = 1 := by
    by_contra hne
    have hTwo : 2 ≤ n := by omega
    let A := Localization.AtPrime P
    have hdimA : (2 : WithBot ℕ∞) ≤ ringKrullDim A := by
      rw [IsLocalization.AtPrime.ringKrullDim_eq_height P A, hheight]
      change ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞)
      apply WithBot.coe_le_coe.mpr
      exact_mod_cast hTwo
    have hfA : algebraMap R A f ∈ maximalIdeal A := by
      change f ∈ (maximalIdeal A).under R
      rw [IsLocalization.AtPrime.under_maximalIdeal A P]
      exact hfP
    obtain ⟨Q, hQ, hfQ, hQpos, hQlt⟩ :=
      exists_positive_height_prime_below_maximal A hdimA (algebraMap R A f) hfA
    have : Q.IsPrime := hQ
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ideal.height_ne_top_of_isPrime (I := Q))
    have hmpos : 1 ≤ m := by
      rw [← hm] at hQpos
      exact_mod_cast hQpos
    have hunder : (Q.under R).height = Q.height := IsLocalization.height_under P.primeCompl Q
    have hmin : n ≤ m := Nat.find_min' hex
      ⟨Q.under R, inferInstance, hfQ, hunder.trans hm.symm, hmpos⟩
    have hlt : Q.height < P.height := by
      apply (Ideal.height_strict_mono_of_isPrime_of_isPrime hQlt).trans_eq
      apply WithBot.coe_injective
      rw [maximalIdeal_height_eq_ringKrullDim,
        IsLocalization.AtPrime.ringKrullDim_eq_height P A]
    rw [← hm, hheight] at hlt
    have hmn : m < n := by exact_mod_cast hlt
    exact (not_lt_of_ge hmin) hmn
  exact ⟨P, hP, hfP, hheight.trans (congrArg (fun k : ℕ => (k : ℕ∞)) hnOne)⟩

/-- In a positive-dimensional Noetherian local ring, every element of the
maximal ideal lies in a prime whose localization has dimension one
(Stacks Project Tag 0BJG). -/
theorem exists_prime_containing_ringKrullDim_localization_eq_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
    (f : R) (hf : f ∈ maximalIdeal R) :
    ∃ (P : Ideal R) (_ : P.IsPrime), f ∈ P ∧
      ringKrullDim (Localization.AtPrime P) = 1 := by
  obtain ⟨P, hP, hfP, hheight⟩ := exists_height_one_prime_containing R hdim f hf
  have : P.IsPrime := hP
  refine ⟨P, hP, hfP, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hheight]
  rfl

end SchemeTheory
