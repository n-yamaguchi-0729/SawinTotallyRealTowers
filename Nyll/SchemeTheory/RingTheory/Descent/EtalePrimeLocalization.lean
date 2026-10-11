/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Etaleness at a point from localization on the base

The prime-local comparison is extracted from
`EtaleFundamentalGroups.Purity.SpecialLocal.BaseMinimalPrimePuncturedPurity`.
It uses the actual iterated-localization isomorphism and requires no
normality, finiteness, or global geometric hypotheses.
-/

noncomputable section

namespace SchemeTheory

universe u

/-- Etaleness of the simultaneous localization at a base prime descends,
after localizing once more, to the original map at the prime below a target
prime. -/
theorem isEtaleAt_under_of_localizedAlgebra_etale
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (p : PrimeSpectrum R)
    (hEtale : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (Q : PrimeSpectrum
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) :
    Algebra.IsEtaleAt R
      (PrimeSpectrum.comap
        (algebraMap S
          (Localization
            (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl))) Q).asIdeal := by
  let A := Localization.AtPrime p.asIdeal
  let B := Localization
    (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)
  let P : PrimeSpectrum S :=
    PrimeSpectrum.comap (algebraMap S B) Q
  let : Algebra.Etale A B := hEtale
  let : Algebra.FormallyEtale A B := hEtale.formallyEtale
  let : Algebra.FormallyEtale A (Localization.AtPrime Q.asIdeal) :=
    inferInstance
  let : Algebra.FormallyEtale R A :=
    Algebra.FormallyEtale.of_isLocalization p.asIdeal.primeCompl
  let : Algebra.FormallyEtale R (Localization.AtPrime Q.asIdeal) :=
    Algebra.FormallyEtale.comp R A (Localization.AtPrime Q.asIdeal)
  let e : Localization.AtPrime P.asIdeal ≃ₐ[S]
      Localization.AtPrime Q.asIdeal :=
    IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl) Q.asIdeal
  exact Algebra.FormallyEtale.of_equiv (e.restrictScalars R).symm

/-- If a target prime lies over `p`, etaleness of the simultaneous
localization at `p` implies etaleness of the original algebra at that target
prime. -/
theorem isEtaleAt_of_localizedAlgebra_etale
    {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S]
    (p : PrimeSpectrum R)
    (hEtale : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization
        (Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl)))
    (P : PrimeSpectrum S)
    (hPp : PrimeSpectrum.comap (algebraMap R S) P = p) :
    Algebra.IsEtaleAt R P.asIdeal := by
  let M := Algebra.algebraMapSubmonoid S p.asIdeal.primeCompl
  let B := Localization M
  have hdisj : Disjoint (M : Set S) (P.asIdeal : Set S) := by
    rw [Set.disjoint_left]
    intro s hsM hsP
    change s ∈ Submonoid.map (algebraMap R S) p.asIdeal.primeCompl at hsM
    obtain ⟨r, hr, hrs⟩ := hsM
    have hrP : r ∈
        (PrimeSpectrum.comap (algebraMap R S) P).asIdeal := by
      change algebraMap R S r ∈ P.asIdeal
      rwa [hrs]
    rw [hPp] at hrP
    exact hr hrP
  let Q : PrimeSpectrum B :=
    ⟨Ideal.map (algebraMap S B) P.asIdeal,
      IsLocalization.isPrime_of_isPrime_disjoint
        M B P.asIdeal P.isPrime hdisj⟩
  have hunder : PrimeSpectrum.comap (algebraMap S B) Q = P := by
    apply PrimeSpectrum.ext
    exact IsLocalization.under_map_of_isPrime_disjoint
      M B P.isPrime hdisj
  have hQ : Algebra.IsEtaleAt R
      (PrimeSpectrum.comap (algebraMap S B) Q).asIdeal :=
    isEtaleAt_under_of_localizedAlgebra_etale p hEtale Q
  simpa only [hunder] using hQ

end SchemeTheory
