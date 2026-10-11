/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality

import Mathlib.Util.WithWeakNamespace
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Normality of smooth algebras localized at primes

A smooth algebra localized at a prime over an integrally closed domain is a domain and
is integrally closed. The proof first treats polynomial algebras and then the etale
local presentation.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace
  Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
universe u

theorem isIntegrallyClosed_mvPolynomial_fin (R : Type u) [CommRing R]
    [IsDomain R] [IsIntegrallyClosed R] :
    ∀ n : ℕ, IsIntegrallyClosed (MvPolynomial (Fin n) R)
  | 0 => IsIntegrallyClosed.of_equiv (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | n + 1 => by
      have := isIntegrallyClosed_mvPolynomial_fin R n
      exact IsIntegrallyClosed.of_equiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv

with_weak_namespace _root_.AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open
  Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime in
with_weak_namespace _root_.Algebra.Smooth
theorem isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.Smooth R S]
    (p : Ideal S) [p.IsPrime] (Sₚ : Type u) [CommRing Sₚ]
    [Algebra S Sₚ] [IsLocalization.AtPrime Sₚ p] :
    IsDomain Sₚ ∧ IsIntegrallyClosed Sₚ := by
  classical
  have hp : p.IsPrime := inferInstance
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R p
  set Sf := Localization.Away f with hSf
  have : Algebra.IsStandardSmooth R Sf := hstd
  obtain ⟨ι, σ, hσ, hι, ⟨Pr⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R Sf).out
  have : Algebra.IsStandardSmoothOfRelativeDimension Pr.dimension R Sf := ⟨ι, σ, hσ, hι, Pr, rfl⟩
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial Pr.dimension R Sf
  let : Algebra (MvPolynomial (Fin Pr.dimension) R) Sf := g.toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin Pr.dimension) R) Sf := hg
  have hdisj : Disjoint (Submonoid.powers f : Set S) (p : Set S) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  set q : Ideal Sf := p.map (algebraMap S Sf) with hq
  have hqp : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) Sf p hp hdisj
  have hcomap : q.comap (algebraMap S Sf) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f) Sf hp hdisj
  have hunit : IsUnit (algebraMap S Sₚ f) := IsLocalization.map_units Sₚ (⟨f, hf⟩ : p.primeCompl)
  let : Algebra Sf Sₚ := (IsLocalization.Away.lift f hunit).toAlgebra
  have : IsScalarTower S Sf Sₚ := IsScalarTower.of_algebraMap_eq fun s => by
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.lift_eq]
  have hle : Submonoid.powers f ≤ p.primeCompl := by
    rintro _ ⟨k, rfl⟩
    exact fun h => hf (hp.mem_of_pow_mem k h)
  have hloc : IsLocalization (p.primeCompl.map (algebraMap S Sf)) Sₚ :=
    IsLocalization.isLocalization_of_submonoid_le Sf Sₚ (Submonoid.powers f) p.primeCompl hle
  have : IsLocalization.AtPrime Sₚ q := by
    refine IsLocalization.of_le_of_exists_dvd
      (p.primeCompl.map (algebraMap S Sf)) q.primeCompl ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      change algebraMap S Sf s ∉ q
      intro h
      exact hs (by rw [← hcomap]; exact h)
    · intro n hn
      obtain ⟨⟨s, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) n
      have hm : (m : S) ∉ p := Set.disjoint_left.mp hdisj m.2
      have hs : s ∉ p := by
        intro hs
        apply hn
        have hspec : IsLocalization.mk' Sf s m * algebraMap S Sf m = algebraMap S Sf s :=
          IsLocalization.mk'_spec Sf s m
        have hmem : algebraMap S Sf s ∈ q := Ideal.mem_map_of_mem _ hs
        rw [← hspec] at hmem
        rcases hqp.mem_or_mem hmem with h | h
        · exact h
        · exact absurd (show (m : S) ∈ p by rw [← hcomap]; exact h) hm
      exact ⟨algebraMap S Sf s, ⟨s, hs, rfl⟩, algebraMap S Sf m,
        (IsLocalization.mk'_spec Sf s m).symm⟩
  have : IsIntegrallyClosed (MvPolynomial (Fin Pr.dimension) R) :=
    isIntegrallyClosed_mvPolynomial_fin R Pr.dimension
  exact Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
    (MvPolynomial (Fin Pr.dimension) R) Sf q Sₚ
end Algebra_Smooth_isDomain_and_isIntegrallyClosed_of_isIntegrallyClosed_of_isLocalization_atPrime
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
