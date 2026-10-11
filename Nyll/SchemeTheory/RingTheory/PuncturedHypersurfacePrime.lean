/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Nonclosed points of local hypersurfaces

A principal hypersurface in a Noetherian local ring of dimension at least
two contains a prime different from the maximal ideal. The same construction
on a prime quotient produces a point on a specified irreducible component.
-/

open IsLocalRing

namespace SchemeTheory

universe u

/-- A hypersurface in local dimension at least two contains a nonclosed point. -/
theorem exists_prime_containing_ne_maximal_of_two_le_ringKrullDim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim R)
    (f : R) (hf : f ∈ maximalIdeal R) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P ≠ maximalIdeal R := by
  obtain ⟨P, hP, _⟩ := Ideal.exists_minimalPrimes_le
    ((maximalIdeal R).span_singleton_le_iff_mem.mpr hf)
  refine ⟨P, hP.isPrime, hP.le (Ideal.subset_span (Set.mem_singleton f)), ?_⟩
  intro hPm
  have hheight : P.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {f}) P hP
  have hbound : (2 : WithBot ℕ∞) ≤ (1 : WithBot ℕ∞) := by
    apply hdim.trans
    rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← hPm]
    exact WithBot.coe_le_coe.mpr hheight
  norm_num at hbound

/-- The hypersurface meets the puncture on every prime quotient of dimension
at least two. -/
theorem exists_prime_over_containing_ne_maximal_of_two_le_quotient_ringKrullDim
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime]
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P))
    (f : R) (hf : f ∈ maximalIdeal R) :
    ∃ Q : Ideal R, Q.IsPrime ∧ P ≤ Q ∧ f ∈ Q ∧ Q ≠ maximalIdeal R := by
  let q : R →+* R ⧸ P := Ideal.Quotient.mk P
  have : IsLocalRing (R ⧸ P) :=
    IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hqf : q f ∈ maximalIdeal (R ⧸ P) := by
    rw [← maximalIdeal_comap q] at hf
    exact hf
  obtain ⟨Q, hQ, hfQ, hQm⟩ :=
    exists_prime_containing_ne_maximal_of_two_le_ringKrullDim (R ⧸ P) hdim (q f) hqf
  have : Q.IsPrime := hQ
  refine ⟨Q.comap q, inferInstance, ?_, hfQ, ?_⟩
  · intro a ha
    change q a ∈ Q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Q.zero_mem
  · intro hQcomap
    apply hQm
    apply Ideal.comap_injective_of_surjective q Ideal.Quotient.mk_surjective
    exact hQcomap.trans (maximalIdeal_comap q).symm

end SchemeTheory
