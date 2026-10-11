/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.RingHom.Etale

/-!
# Removing an Away localization at a unit

If the distinguished element is already a unit in the target, the target
Away localization is isomorphic to the original target.  This file records
the corresponding descent of etaleness and its target-local application.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB

/-- If the image of `f` is a unit, etaleness of the literal Away map implies
etaleness of the original algebra.  Indeed, the source localization is
etale over the original source and the target localization is isomorphic to
the original target. -/
theorem etale_of_localization_awayMap_of_isUnit_image
    {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] [Algebra A B]
    (f : A) (hfB : IsUnit (algebraMap A B f))
    (hAway : (Localization.awayMap (algebraMap A B) f).Etale) :
    Algebra.Etale A B := by
  let S := Localization.Away f
  let fB : B := algebraMap A B f
  let T := Localization.Away fB
  let mapST : S →+* T := Localization.awayMap (algebraMap A B) f
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap A T a = mapST (algebraMap A S a)
    rw [IsScalarTower.algebraMap_apply A B T]
    simp [mapST, S, T, fB, IsLocalization.Away.map]
  let : Algebra.Etale S T := hAway.toAlgebra
  let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway f
  let : Algebra.Etale A T := Algebra.Etale.comp A S T
  let eTarget : T ≃ₐ[B] B :=
    (IsLocalization.atUnit B T fB hfB).symm
  exact Algebra.Etale.of_equiv (eTarget.restrictScalars A)

/-- A local-local criterion for the literal Away map, indexed by the primes
of the unlocalized target that survive the Away localization.  This is the
form naturally supplied by normalization-localization comparisons. -/
theorem localization_awayMap_etale_of_etale_localizationsAtPrime
    {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B]
    (f : A)
    (hlocal : ∀ (Q : Ideal B), [Q.IsPrime] →
      algebraMap A B f ∉ Q →
      let p := Q.under A
      letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
        Localization.AtPrime.algebraOfLiesOver p Q
      Algebra.Etale (Localization.AtPrime p) (Localization.AtPrime Q)) :
    (Localization.awayMap (algebraMap A B) f).Etale := by
  let S := Localization.Away f
  let fB : B := algebraMap A B f
  let T := Localization.Away fB
  let mapST : S →+* T := Localization.awayMap (algebraMap A B) f
  have hAT : Algebra.Etale A T := by
    apply Algebra.basicOpen_subset_etaleLocus_iff_etale.mp
    intro Q hQ
    let p := Q.asIdeal.under A
    let : Algebra (Localization.AtPrime p)
        (Localization.AtPrime Q.asIdeal) :=
      Localization.AtPrime.algebraOfLiesOver p Q.asIdeal
    let : Algebra.Etale (Localization.AtPrime p)
        (Localization.AtPrime Q.asIdeal) :=
      hlocal Q.asIdeal ((PrimeSpectrum.mem_basicOpen _ _).mp hQ)
    let : Algebra.FormallyEtale A (Localization.AtPrime p) :=
      Algebra.FormallyEtale.of_isLocalization p.primeCompl
    change Algebra.FormallyEtale A (Localization.AtPrime Q.asIdeal)
    exact Algebra.FormallyEtale.comp A (Localization.AtPrime p)
      (Localization.AtPrime Q.asIdeal)
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap A T a = mapST (algebraMap A S a)
    rw [IsScalarTower.algebraMap_apply A B T]
    simp [mapST, S, T, fB, IsLocalization.Away.map]
  let : Algebra.Etale A S := Algebra.Etale.of_isLocalizationAway f
  let : Algebra.Etale A T := hAT
  exact Algebra.Etale.of_restrictScalars A S T

/-- A version of
`localization_awayMap_etale_of_etale_localizationsAtPrime` whose local input
is itself a literal Away map.  At a target prime avoiding the distinguished
element, that element is a unit in the target local ring, so the auxiliary
Away localization can be removed by
`etale_of_localization_awayMap_of_isUnit_image`. -/
theorem localization_awayMap_etale_of_local_awayMapsAtPrime
    {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B]
    (f : A)
    (hlocal : ∀ (Q : Ideal B), [Q.IsPrime] →
      algebraMap A B f ∉ Q →
      let p := Q.under A
      letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
        Localization.AtPrime.algebraOfLiesOver p Q
      let fp : Localization.AtPrime p :=
        algebraMap A (Localization.AtPrime p) f
      (Localization.awayMap
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q))
        fp).Etale) :
    (Localization.awayMap (algebraMap A B) f).Etale := by
  apply localization_awayMap_etale_of_etale_localizationsAtPrime f
  intro Q _ hfQ
  let p := Q.under A
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver p Q
  let fp : Localization.AtPrime p :=
    algebraMap A (Localization.AtPrime p) f
  apply etale_of_localization_awayMap_of_isUnit_image fp
  · have hunit :
        IsUnit (algebraMap B (Localization.AtPrime Q)
          (algebraMap A B f)) :=
      IsLocalization.map_units (Localization.AtPrime Q)
        (M := Q.primeCompl) ⟨algebraMap A B f, hfQ⟩
    have hEq :
        algebraMap (Localization.AtPrime p) (Localization.AtPrime Q) fp =
          algebraMap B (Localization.AtPrime Q) (algebraMap A B f) := by
      dsimp only [fp]
      rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime p)
        (Localization.AtPrime Q),
        ← IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q)]
    rw [hEq]
    exact hunit
  · exact hlocal Q hfQ

/-- Ring-map form of
`localization_awayMap_etale_of_local_awayMapsAtPrime`.  The conclusion keeps
the supplied map literally, which is useful for a composite normalization
map whose ambient `Algebra` instance is not canonical. -/
theorem ringHom_localization_awayMap_etale_of_local_awayMapsAtPrime
    {A : Type uA} {B : Type uB}
    [CommRing A] [CommRing B]
    (mapAB : A →+* B) (hfp : mapAB.FinitePresentation)
    (f : A)
    (hlocal :
      letI : Algebra A B := mapAB.toAlgebra
      ∀ (Q : Ideal B), [Q.IsPrime] →
        mapAB f ∉ Q →
        let p := Q.under A
        letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver p Q
        let fp : Localization.AtPrime p :=
          algebraMap A (Localization.AtPrime p) f
        (Localization.awayMap
          (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q))
          fp).Etale) :
    (Localization.awayMap mapAB f).Etale := by
  let : Algebra A B := mapAB.toAlgebra
  let : Algebra.FinitePresentation A B := hfp
  exact localization_awayMap_etale_of_local_awayMapsAtPrime f hlocal

end EtaleFundamentalGroups

end
