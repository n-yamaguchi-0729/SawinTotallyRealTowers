/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Spreading unramifiedness around an integral fiber

The unramified locus of a finite type algebra is open without a finite
presentation assumption. Its closed complement has closed image under an
integral map, so unramifiedness of one entire fiber spreads to a principal
neighborhood of the base point.
-/

namespace SchemeTheory

universe u v

/-- An integral finite type algebra unramified at every prime above `p` is
formally unramified on a principal neighborhood of that entire fiber. -/
theorem exists_unramified_away_of_isUnramifiedAt_fiber
    {R : Type u} {B : Type v} [CommRing R] [CommRing B]
    [Algebra R B] [Algebra.IsIntegral R B] [Algebra.FiniteType R B]
    (p : PrimeSpectrum R)
    (hunramified : ∀ P : PrimeSpectrum B,
      PrimeSpectrum.comap (algebraMap R B) P = p → Algebra.IsUnramifiedAt R P.asIdeal) :
    ∃ r : R, r ∉ p.asIdeal ∧
      Algebra.FormallyUnramified R (Localization.Away (algebraMap R B r)) := by
  let f := PrimeSpectrum.comap (algebraMap R B)
  let Z : Set (PrimeSpectrum R) := f '' (Algebra.unramifiedLocus R B)ᶜ
  have hclosed : IsClosed Z :=
    PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R B)
      (algebraMap_isIntegral_iff.mpr inferInstance)
      _ Algebra.isOpen_unramifiedLocus.isClosed_compl
  have hp : p ∈ Zᶜ := by
    rintro ⟨P, hP, hPp⟩
    exact hP (hunramified P hPp)
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hp hclosed.isOpen_compl
  refine ⟨r, hpr, Algebra.basicOpen_subset_unramifiedLocus_iff.mp ?_⟩
  intro P hP
  by_contra hnot
  have hfp : f P ∈ PrimeSpectrum.basicOpen r := hP
  exact (hr hfp) ⟨P, hnot, rfl⟩

end SchemeTheory
