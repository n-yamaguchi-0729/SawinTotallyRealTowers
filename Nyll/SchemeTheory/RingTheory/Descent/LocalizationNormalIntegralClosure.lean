/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing


/-!
# Integral closure in a localization with normal boundary local rings

An integral fraction has locally divisible numerator at each maximal ideal.
At a maximal ideal meeting the denominator submonoid, normality gives that
divisibility in the prime localization. At the other maximal ideals the
denominator is already a unit. Global divisibility then gives an element of
the original ring. No principal denominator or noetherian hypothesis is used.
-/

noncomputable section

namespace SchemeTheory

open scoped nonZeroDivisors

universe u v

/-- A ring is integrally closed in a localization by non-zero-divisors if its
local rings at maximal ideals meeting the denominator submonoid are normal. -/
theorem isIntegrallyClosedIn_localization_of_normal_boundary
    {R : Type u} [CommRing R] (M : Submonoid R) (hM : M ≤ R⁰)
    (T : Type v) [CommRing T] [Algebra R T] [IsLocalization M T]
    (hnormal : ∀ (p : Ideal R) [p.IsMaximal], (∃ s : M, (s : R) ∈ p) →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosedIn R T := by
  refine isIntegrallyClosedIn_iff.mpr ⟨IsLocalization.injective T hM, ?_⟩
  intro y hy
  obtain ⟨⟨a, s⟩, ha⟩ := IsLocalization.surj M y
  have hdiv : (s : R) ∣ a := by
    apply Ideal.mem_span_singleton.mp
    apply Ideal.mem_of_localization_maximal
    intro p hp
    let Rp := Localization.AtPrime p
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
    by_cases hsp : (s : R) ∈ p
    · have : IsDomain Rp := (hnormal p ⟨s, hsp⟩).1
      have : IsIntegrallyClosed Rp := (hnormal p ⟨s, hsp⟩).2
      let F := FractionRing Rp
      let g : T →ₐ[R] F := IsLocalization.liftAlgHom (M := M)
        (f := Algebra.ofId R F) (fun m => by
          apply isUnit_iff_ne_zero.mpr
          change algebraMap R F (m : R) ≠ 0
          rw [IsScalarTower.algebraMap_apply R Rp F]
          exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
            (IsLocalization.nonZeroDivisors_le_comap p.primeCompl Rp (hM m.property)))
      have hyF : IsIntegral Rp (g y) := (hy.map g).tower_top
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hyF
      refine ⟨b, IsFractionRing.injective Rp F ?_⟩
      have hga : g y * algebraMap R F (s : R) = algebraMap R F a := by
        simpa only [map_mul, AlgHom.commutes] using congrArg g ha
      calc
        algebraMap Rp F (algebraMap R Rp a) = algebraMap R F a :=
          (IsScalarTower.algebraMap_apply R Rp F a).symm
        _ = g y * algebraMap R F (s : R) := hga.symm
        _ = algebraMap R F (s : R) * algebraMap Rp F b := by rw [hb, mul_comm]
        _ = algebraMap Rp F (algebraMap R Rp (s : R) * b) := by
          rw [map_mul, IsScalarTower.algebraMap_apply R Rp F]
    · exact (IsLocalization.map_units Rp (⟨s, hsp⟩ : p.primeCompl)).dvd
  obtain ⟨b, hb⟩ := hdiv
  refine ⟨b, ?_⟩
  apply (IsLocalization.map_units T s).mul_right_cancel
  calc
    algebraMap R T b * algebraMap R T (s : R) = algebraMap R T ((s : R) * b) := by
      rw [map_mul, mul_comm]
    _ = algebraMap R T a := congrArg (algebraMap R T) hb.symm
    _ = y * algebraMap R T (s : R) := ha.symm

end SchemeTheory
