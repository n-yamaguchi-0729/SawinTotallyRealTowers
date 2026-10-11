/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.EtaleSource
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatOnOpenImage
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.TensorProduct.Basic


/-!
# A genuine étale principal neighborhood in the image of an étale source

For R → S → T with S → T and R → T étale, every prime of S in the
actual image of Spec T has a principal neighborhood étale over R. The open
image supplies its defining ideal. Localizing at an element of that ideal
makes the source cover faithfully flat, and genuine source étale descent
supplies finite presentation as well as formal étaleness.
-/

open scoped TensorProduct

namespace SchemeTheory

universe u v w

/-- Étaleness of a source cover and its composite supplies a genuine étale
principal neighborhood around each point in the actual source image. -/
theorem exists_etale_away_of_mem_image_etale_source
    (R : Type u) (S : Type v) (T : Type w)
    [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.Etale S T] [Algebra.Etale R T]
    (p : PrimeSpectrum S)
    (hp : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S T))) :
    ∃ f : S, f ∉ p.asIdeal ∧ Algebra.Etale R (Localization.Away f) := by
  obtain ⟨J, hJ⟩ := PrimeSpectrum.exists_ideal_range_comap_of_flat_of_finitePresentation
    (A₀ := S) (B₀ := T)
  have hnot : ¬ (J : Set S) ⊆ (p.asIdeal : Set S) := (hJ p).mp hp
  obtain ⟨f, hfJ, hfp⟩ := Set.not_subset.mp hnot
  refine ⟨f, hfp, ?_⟩
  let Sf := Localization.Away f
  let C := Sf ⊗[S] T
  have htop : J.map (algebraMap S Sf) = ⊤ :=
    (J.map (algebraMap S Sf)).eq_top_of_isUnit_mem
      (Ideal.mem_map_of_mem (algebraMap S Sf) hfJ)
      (IsLocalization.Away.algebraMap_isUnit f)
  have : Module.FaithfullyFlat Sf C :=
    Module.Flat.faithfullyFlat_baseChange_of_map_eq_top J (fun q hq => (hJ q).mpr hq) Sf htop
  let : Algebra T C := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower R T C := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R C r =
      Algebra.TensorProduct.includeRight (R := S) (A := Sf) (B := T) (algebraMap R T r)
    rw [IsScalarTower.algebraMap_apply R S T,
      (Algebra.TensorProduct.includeRight (R := S) (A := Sf) (B := T)).commutes,
      ← IsScalarTower.algebraMap_apply R S C])
  have : Algebra.Etale T C :=
    Algebra.Etale.of_isLocalizationAway (algebraMap S T f)
  have : Algebra.Etale R C := Algebra.Etale.comp R T C
  exact etale_of_faithfullyFlat_of_etale R Sf C

end SchemeTheory
