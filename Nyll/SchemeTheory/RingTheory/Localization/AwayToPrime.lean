/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Localization.AwayAlgebra
import Nyll.SchemeTheory.RingTheory.Localization.SubalgebraPrime
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.OreLocalization.Ring

/-!
# Native principal-localization maps to an actual prime localization

The source is the actual native principal localization. The target and its
coefficient map are the existing native prime-localization owners. The single
localization proof below closes the coefficient equation in an R/C-only scope.
The base equation then uses only that proved equation and an ordinary
coefficient-ring square, supplied in applications by the original inclusion.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- The actual native principal localization, bundled with its native ring. -/
def principalLocalizationCommRingCat (R : Type v) [CommRing R] (d : R) :
    CommRingCat.{v} :=
  CommRingCat.of (localizationAwayCommAlgCat R R d)

/-- The native coefficient map into the actual principal localization. -/
def principalLocalizationCoefficientMap (R : Type v) [CommRing R] (d : R) :
    R →+* principalLocalizationCommRingCat R d :=
  algebraMap R (localizationAwayCommAlgCat R R d)

/-- A coefficient outside the actual prime becomes a unit under the computed
native prime-localization map. This closes the target localization algebra
before the principal-localization lift is used. -/
theorem primeLocalizationCoefficientMap_comp_isUnit
    {R : Type v} {C : Type w} [CommRing R] [CommRing C]
    (f : R →+* C) (d : R) (Q : Ideal C) [Q.IsPrime] (h : f d ∉ Q) :
    IsUnit (((primeLocalizationCoefficientMap C Q).comp f) d) := by
  exact IsLocalization.map_units (Localization.AtPrime Q) (⟨f d, h⟩ : Q.primeCompl)

/-- The native principal-localization lift of the actual coefficient map. -/
def principalLocalizationToPrimeMap
    {R : Type v} {C : Type w} [CommRing R] [CommRing C]
    (f : R →+* C) (d : R) (Q : Ideal C) [Q.IsPrime] (h : f d ∉ Q) :
    principalLocalizationCommRingCat R d →+* primeLocalizationCommRingCat C Q := by
  have : IsLocalization.Away d (localizationAwayCommAlgCat R R d) :=
    localizationAwayCommAlgCat_isLocalization R d
  exact IsLocalization.Away.lift (S := localizationAwayCommAlgCat R R d) d
    (g := (primeLocalizationCoefficientMap C Q).comp f)
    (primeLocalizationCoefficientMap_comp_isUnit f d Q h)

/-- The native coefficient equation, retained as an equality of computed
RingHoms so later applications do not reopen the localization algebras. -/
theorem principalLocalizationToPrimeMap_comp_coefficient
    {R : Type v} {C : Type w} [CommRing R] [CommRing C]
    (f : R →+* C) (d : R) (Q : Ideal C) [Q.IsPrime] (h : f d ∉ Q) :
    (principalLocalizationToPrimeMap f d Q h).comp
        (principalLocalizationCoefficientMap R d) =
      (primeLocalizationCoefficientMap C Q).comp f := by
  have : IsLocalization.Away d (localizationAwayCommAlgCat R R d) :=
    localizationAwayCommAlgCat_isLocalization R d
  apply RingHom.ext
  intro r
  exact IsLocalization.Away.lift_eq (S := localizationAwayCommAlgCat R R d) d
    (g := (primeLocalizationCoefficientMap C Q).comp f)
    (primeLocalizationCoefficientMap_comp_isUnit f d Q h) r

/-- The original base-ring map into the actual principal localization. -/
def principalLocalizationBaseMap (A : Type u) (R : Type v)
    [CommRing A] [CommRing R] [Algebra A R] (d : R) :
    A →+* principalLocalizationCommRingCat R d :=
  (principalLocalizationCoefficientMap R d).comp (algebraMap A R)

/-- The computed base map is the existing principal-localization algebra
map. The scalar tower is the native one; no new action is installed. -/
theorem principalLocalizationBaseMap_eq_algebraMap
    (A : Type u) (R : Type v) [CommRing A] [CommRing R] [Algebra A R] (d : R) :
    principalLocalizationBaseMap A R d =
      algebraMap A (localizationAwayCommAlgCat A R d) := by
  exact (IsScalarTower.algebraMap_eq A R (Localization.Away d)).symm

/-- An ordinary base square on the coefficient rings gives the closed
base square for the actual principal-localization lift. -/
theorem principalLocalizationToPrimeMap_comp_base
    (A : Type u) {R : Type v} {C : Type w}
    [CommRing A] [CommRing R] [CommRing C] [Algebra A R] [Algebra A C]
    (f : R →+* C) (d : R) (Q : Ideal C) [Q.IsPrime] (h : f d ∉ Q)
    (hbase : f.comp (algebraMap A R) = algebraMap A C) :
    (principalLocalizationToPrimeMap f d Q h).comp
        (principalLocalizationBaseMap A R d) =
      primeLocalizationBaseMap A C Q := by
  let b : R →+* principalLocalizationCommRingCat R d :=
    principalLocalizationCoefficientMap R d
  let c : C →+* primeLocalizationCommRingCat C Q :=
    primeLocalizationCoefficientMap C Q
  have hlocal : (principalLocalizationToPrimeMap f d Q h).comp b = c.comp f :=
    principalLocalizationToPrimeMap_comp_coefficient f d Q h
  calc
    (principalLocalizationToPrimeMap f d Q h).comp (principalLocalizationBaseMap A R d) =
        ((principalLocalizationToPrimeMap f d Q h).comp b).comp (algebraMap A R) :=
      (RingHom.comp_assoc (algebraMap A R) b
        (principalLocalizationToPrimeMap f d Q h)).symm
    _ = (c.comp f).comp (algebraMap A R) :=
      congrArg (fun k : R →+* primeLocalizationCommRingCat C Q =>
        k.comp (algebraMap A R)) hlocal
    _ = c.comp (f.comp (algebraMap A R)) :=
      RingHom.comp_assoc (algebraMap A R) f c
    _ = primeLocalizationBaseMap A C Q :=
      congrArg (fun k : A →+* C => c.comp k) hbase

end SchemeTheory
