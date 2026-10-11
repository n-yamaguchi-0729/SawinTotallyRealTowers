/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Spreading etaleness around a fiber of an integral algebra

The complement of the etale locus has closed image under an integral map.
A fiber contained in the etale locus therefore has an entire principal
neighborhood contained in that locus.
-/

namespace SchemeTheory

universe u v

/-- If an integral finitely presented algebra is etale at every prime over
`p`, it is etale on the preimage of a principal neighborhood of `p`. -/
theorem exists_etale_away_of_isEtaleAt_fiber
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Algebra.FinitePresentation R B]
    (p : PrimeSpectrum R)
    (hetale : ∀ P : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap R B) P = p → Algebra.IsEtaleAt R P.asIdeal) :
    ∃ r : R, r ∉ p.asIdeal ∧ Algebra.Etale R (Localization.Away (algebraMap R B r)) := by
  let f := PrimeSpectrum.comap (algebraMap R B)
  let Z : Set (PrimeSpectrum R) := f '' (Algebra.etaleLocus R B)ᶜ
  have hclosed : IsClosed Z :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R B)
      (algebraMap_isIntegral_iff.mpr inferInstance)
      _ Algebra.isOpen_etaleLocus.isClosed_compl
  have hp : p ∈ Zᶜ := by
    rintro ⟨P, hP, hPp⟩
    exact hP (hetale P hPp)
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp hclosed.isOpen_compl
  refine ⟨r, hpr, Algebra.basicOpen_subset_etaleLocus_iff_etale.mp ?_⟩
  intro P hP
  by_contra hnot
  have hfp : f P ∈ PrimeSpectrum.basicOpen r := hP
  exact (hr hfp) ⟨P, hnot, rfl⟩

end SchemeTheory
