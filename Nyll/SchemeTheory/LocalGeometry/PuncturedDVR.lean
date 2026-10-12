/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Nyll.SchemeTheory.RingTheory.DVRFractionFieldAway
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The punctured spectrum of a discrete valuation ring

The fraction field of a DVR is its localization away from any uniformizer.
Consequently its spectrum is the actual open complement of the closed
point. The resulting scheme isomorphism retains the canonical map to the
full spectrum, so covers of the puncture and of the fraction field can be
compared without replacing their structure maps.
-/

noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry.Scheme

universe u

/-- The puncture of a DVR is the principal open of any uniformizer. -/
theorem puncturedSpectrumOpen_eq_basicOpen_of_uniformizer
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {π : R} (hπ : Irreducible π) :
    puncturedSpectrumOpen R = PrimeSpectrum.basicOpen π := by
  ext p
  change p ≠ closedPoint R ↔ π ∉ p.asIdeal
  constructor
  · intro hp hπp
    apply hp
    apply PrimeSpectrum.ext
    change p.asIdeal = maximalIdeal R
    apply le_antisymm (le_maximalIdeal p.isPrime.ne_top)
    rw [hπ.maximalIdeal_eq]
    exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hπp
  · intro hp hpc
    apply hp
    rw [hpc]
    change π ∈ maximalIdeal R
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π

/-- The canonical map from a DVR's fraction-field spectrum is an open
immersion. Its localization presentation is derived from the DVR. -/
theorem isOpenImmersion_SpecMap_fractionField_of_dvr
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π K :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      R K π hπ.ne_zero hπ.not_isUnit
  exact IsOpenImmersion.of_isLocalization π

/-- The canonical fraction-field spectrum has exactly the puncture as its
image, with the original `R`-algebra structure on the fraction field. -/
theorem range_SpecMap_fractionField_of_dvr
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Set.range (Spec.map (CommRingCat.ofHom (algebraMap R K))) =
      (puncturedSpectrumOpen R : Set (Spec (.of R))) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away π K :=
    SchemeTheory.isLocalizationAway_fractionField_of_isDiscreteValuationRing
      R K π hπ.ne_zero hπ.not_isUnit
  change Set.range (PrimeSpectrum.comap (algebraMap R K)) = _
  exact (PrimeSpectrum.localization_away_comap_range K π).trans
    (congrArg (fun U : (Spec (.of R)).Opens => (U : Set (Spec (.of R))))
      (puncturedSpectrumOpen_eq_basicOpen_of_uniformizer R hπ).symm)

/-- The puncture of a DVR is its fraction-field spectrum, as schemes over
that DVR. -/
def puncturedSpectrumIsoSpecFractionField
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    puncturedSpectrum R ≅ Spec (.of K) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    isOpenImmersion_SpecMap_fractionField_of_dvr R K
  exact IsOpenImmersion.isoOfRangeEq (puncturedSpectrumOpen R).ι
    (Spec.map (CommRingCat.ofHom (algebraMap R K))) (by
      rw [Opens.range_ι]
      exact (range_SpecMap_fractionField_of_dvr R K).symm)

/-- The puncture/fraction-field comparison preserves the map to `Spec R`. -/
@[reassoc]
theorem puncturedSpectrumIsoSpecFractionField_hom_SpecMap
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    (puncturedSpectrumIsoSpecFractionField R K).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R K)) =
      puncturedSpectrumInclusion R := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    isOpenImmersion_SpecMap_fractionField_of_dvr R K
  exact IsOpenImmersion.isoOfRangeEq_hom_fac (puncturedSpectrumOpen R).ι
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))
    ((Opens.range_ι (puncturedSpectrumOpen R)).trans
      (range_SpecMap_fractionField_of_dvr R K).symm)

end AlgebraicGeometry.Scheme
