/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Nyll.SchemeTheory.RingTheory.Localization.AwayAlgebra
import Nyll.SchemeTheory.RingTheory.Localization.AwayToPrime
import Nyll.SchemeTheory.RingTheory.Localization.SubalgebraPrime
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Defs

/-!
# Actual principal and prime localization objects over a fixed base

The objects retain their existing native commutative algebra structures.
The maps are the already proved native RingHoms. The contracted ideal is
computed before its membership condition is used, so the public map and
coefficient equation mention only the computed ideal and objects.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- The actual native principal localization with its original base algebra. -/
def commAlgPrincipalLocalization {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (d : R) : CommAlgCat.{v} A :=
  localizationAwayCommAlgCat A R d

/-- The actual native prime localization with its original base algebra. -/
def commAlgPrimeLocalization {A : Type u} [CommRing A]
    (S : CommAlgCat.{v} A) (p : Ideal S) [p.IsPrime] : CommAlgCat.{v} A :=
  CommAlgCat.of A (Localization.AtPrime p)

/-- The literal contraction of the chosen ideal along the coefficient map. -/
def commAlgContractionIdeal {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (p : Ideal S) : Ideal R :=
  p.comap f

/-- The existing native principal-localization coefficient RingHom. -/
def commAlgPrincipalCoefficientMap {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (d : R) : R →+* commAlgPrincipalLocalization R d :=
  principalLocalizationCoefficientMap R d

/-- The existing native prime-localization coefficient RingHom. -/
def commAlgPrimeCoefficientMap {A : Type u} [CommRing A]
    (S : CommAlgCat.{v} A) (p : Ideal S) [p.IsPrime] :
    S →+* commAlgPrimeLocalization S p :=
  primeLocalizationCoefficientMap S p

/-- The proved native localization map, with its denominator condition
expressed in the actual computed contraction. -/
def commAlgPrincipalToPrimeMap {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (d : R) (p : Ideal S) [p.IsPrime]
    (h : d ∉ commAlgContractionIdeal R S f p) :
    commAlgPrincipalLocalization R d →+* commAlgPrimeLocalization S p :=
  principalLocalizationToPrimeMap f d p h

/-- The existing native coefficient equation for the actual algebra objects. -/
theorem commAlgPrincipalToPrimeMap_comp_coefficient {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (d : R) (p : Ideal S) [p.IsPrime]
    (h : d ∉ commAlgContractionIdeal R S f p) :
    (commAlgPrincipalToPrimeMap R S f d p h).comp
        (commAlgPrincipalCoefficientMap R d) =
      (commAlgPrimeCoefficientMap S p).comp f := by
  exact principalLocalizationToPrimeMap_comp_coefficient f d p h

/-- The actual principal coefficient map preserves the original base map,
by the already proved native scalar-tower equation. -/
theorem commAlgPrincipalCoefficientMap_comp_base {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (d : R) :
    (commAlgPrincipalCoefficientMap R d).comp (commAlgCoefficientMap R) =
      commAlgCoefficientMap (commAlgPrincipalLocalization R d) := by
  exact principalLocalizationBaseMap_eq_algebraMap A R d

/-- The native prime coefficient map is injective for a domain. This closes
its localization algebra before the principal-map argument. -/
private theorem nativePrimeCoefficientMap_injective
    (S : Type v) [CommRing S] [IsDomain S] (p : Ideal S) [p.IsPrime] :
    Function.Injective (primeLocalizationCoefficientMap S p).toFun := by
  exact IsLocalization.injective (R := S) (M := p.primeCompl)
    (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors

/-- The native principal-localization injectivity argument shared with
the original finite-level colimit owner. Its coefficient map and target
remain in a ring-only scope. -/
theorem principalLocalization_injective_of_coefficient_injective
    {R : Type v} [CommRing R] (d : R) {T : Type w} [CommSemiring T]
    (j : principalLocalizationCommRingCat R d →+* T)
    (hj : Function.Injective
      (j.comp (principalLocalizationCoefficientMap R d)).toFun) :
    Function.Injective j.toFun := by
  have : IsLocalization.Away d (localizationAwayCommAlgCat R R d) :=
    localizationAwayCommAlgCat_isLocalization R d
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (R := R) (S := localizationAwayCommAlgCat R R d) (T := T)
    (Submonoid.powers d) j).mpr
  intro x y
  constructor
  · intro heq
    exact congrArg j.toFun heq
  · intro heq
    exact congrArg (principalLocalizationCoefficientMap R d).toFun (hj heq)

/-- An injective actual coefficient map gives an injective actual
principal-to-prime map. The coefficient square and prime coefficient
injectivity are both proved, rather than compatibility premises. -/
theorem commAlgPrincipalToPrimeMap_injective {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (d : R) (p : Ideal S) [p.IsPrime]
    (h : d ∉ commAlgContractionIdeal R S f p) [IsDomain S]
    (hf : Function.Injective f.toFun) :
    Function.Injective (commAlgPrincipalToPrimeMap R S f d p h).toFun := by
  have hprime : Function.Injective (commAlgPrimeCoefficientMap S p).toFun :=
    nativePrimeCoefficientMap_injective S p
  have hcoeff : Function.Injective
      ((commAlgPrincipalToPrimeMap R S f d p h).comp
        (commAlgPrincipalCoefficientMap R d)).toFun := by
    rw [commAlgPrincipalToPrimeMap_comp_coefficient R S f d p h]
    exact hprime.comp hf
  exact principalLocalization_injective_of_coefficient_injective (R := R) d
    (T := commAlgPrimeLocalization S p) (commAlgPrincipalToPrimeMap R S f d p h) hcoeff

/-- A transported divisor becomes a unit in the target principal localization.
The target localization algebra is used only in this coefficient-ring scope. -/
private theorem principalCoefficientMap_comp_isUnit_of_dvd
    {R S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (r : R) (s : S) (h : f.toFun r ∣ s) :
    IsUnit (((principalLocalizationCoefficientMap S s).comp f).toFun r) := by
  have : IsLocalization.Away s (localizationAwayCommAlgCat S S s) :=
    localizationAwayCommAlgCat_isLocalization S s
  exact IsLocalization.Away.isUnit_of_dvd
    (S := localizationAwayCommAlgCat S S s) s h

/-- The actual native principal-localization transition determined by a
coefficient map and the divisibility of its transported denominator. -/
def commAlgPrincipalTransitionMap {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S)
    (r : R) (s : S) (h : f.toFun r ∣ s) :
    commAlgPrincipalLocalization R r →+* commAlgPrincipalLocalization S s := by
  have : IsLocalization.Away r (localizationAwayCommAlgCat R R r) :=
    localizationAwayCommAlgCat_isLocalization R r
  exact IsLocalization.Away.lift (S := localizationAwayCommAlgCat R R r) r
    (g := (commAlgPrincipalCoefficientMap S s).comp f)
    (principalCoefficientMap_comp_isUnit_of_dvd f r s h)

/-- The transition's coefficient equation is supplied by the native lift. -/
theorem commAlgPrincipalTransitionMap_comp_coefficient
    {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S)
    (r : R) (s : S) (h : f.toFun r ∣ s) :
    (commAlgPrincipalTransitionMap R S f r s h).comp
        (commAlgPrincipalCoefficientMap R r) =
      (commAlgPrincipalCoefficientMap S s).comp f := by
  have : IsLocalization.Away r (localizationAwayCommAlgCat R R r) :=
    localizationAwayCommAlgCat_isLocalization R r
  exact IsLocalization.Away.lift_comp
    (S := localizationAwayCommAlgCat R R r) r
    (g := (commAlgPrincipalCoefficientMap S s).comp f)
    (principalCoefficientMap_comp_isUnit_of_dvd f r s h)

/-- Equality on the native coefficient RingHom determines a map out of the
actual principal localization. Its native scalar action stays in this owner. -/
theorem commAlgPrincipalRingHom_ext
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A) (r : R)
    {T : Type v} [CommSemiring T]
    {f g : commAlgPrincipalLocalization R r →+* T}
    (h : f.comp (commAlgPrincipalCoefficientMap R r) =
      g.comp (commAlgPrincipalCoefficientMap R r)) : f = g := by
  have : IsLocalization.Away r (localizationAwayCommAlgCat R R r) :=
    localizationAwayCommAlgCat_isLocalization R r
  exact IsLocalization.ringHom_ext (R := R)
    (S := localizationAwayCommAlgCat R R r) (Submonoid.powers r) h

/-- An actual coefficient triangle induces the naturality equation for the
native principal-to-prime maps. The principal transition and both coefficient
equations are constructed above; no localization-map equality is assumed. -/
theorem commAlgPrincipalToPrimeMap_naturality
    {A : Type u} [CommRing A] (R S T : CommAlgCat.{v} A)
    (f : R →+* S) (g : S →+* T) (k : R →+* T)
    (hcoeff : g.comp f = k) (r : R) (s : S) (hdiv : f.toFun r ∣ s)
    (p : Ideal T) [p.IsPrime]
    (hr : r ∉ commAlgContractionIdeal R T k p)
    (hs : s ∉ commAlgContractionIdeal S T g p) :
    (commAlgPrincipalToPrimeMap S T g s p hs).comp
        (commAlgPrincipalTransitionMap R S f r s hdiv) =
      commAlgPrincipalToPrimeMap R T k r p hr := by
  let t : commAlgPrincipalLocalization R r →+* commAlgPrincipalLocalization S s :=
    commAlgPrincipalTransitionMap R S f r s hdiv
  let jR : commAlgPrincipalLocalization R r →+* commAlgPrimeLocalization T p :=
    commAlgPrincipalToPrimeMap R T k r p hr
  let jS : commAlgPrincipalLocalization S s →+* commAlgPrimeLocalization T p :=
    commAlgPrincipalToPrimeMap S T g s p hs
  let bR : R →+* commAlgPrincipalLocalization R r := commAlgPrincipalCoefficientMap R r
  let bS : S →+* commAlgPrincipalLocalization S s := commAlgPrincipalCoefficientMap S s
  let c : T →+* commAlgPrimeLocalization T p := commAlgPrimeCoefficientMap T p
  apply commAlgPrincipalRingHom_ext R r
  calc
    (jS.comp t).comp bR = jS.comp (t.comp bR) := RingHom.comp_assoc bR t jS
    _ = jS.comp (bS.comp f) :=
      congrArg (fun l : R →+* commAlgPrincipalLocalization S s => jS.comp l)
        (commAlgPrincipalTransitionMap_comp_coefficient R S f r s hdiv)
    _ = (jS.comp bS).comp f := (RingHom.comp_assoc f bS jS).symm
    _ = (c.comp g).comp f :=
      congrArg (fun l : S →+* commAlgPrimeLocalization T p => l.comp f)
        (commAlgPrincipalToPrimeMap_comp_coefficient S T g s p hs)
    _ = c.comp (g.comp f) := RingHom.comp_assoc f g c
    _ = c.comp k := congrArg (fun l : R →+* T => c.comp l) hcoeff
    _ = jR.comp bR := (commAlgPrincipalToPrimeMap_comp_coefficient R T k r p hr).symm

/-- The actual prime localization at the contraction, retaining its original
base algebra before it is used by a geometric caller. -/
def commAlgPrimeComapLocalization {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (p : Ideal S) [p.IsPrime] :
    CommAlgCat.{v} A := by
  have : (p.comap f).IsPrime := Ideal.IsPrime.comap f
  exact commAlgPrimeLocalization R (p.comap f)

/-- The native coefficient map into the actual contracted-prime object. -/
def commAlgPrimeComapCoefficientMap {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (p : Ideal S) [p.IsPrime] :
    R →+* commAlgPrimeComapLocalization R S f p :=
  primeLocalizationComapCoefficientMap f p

/-- The existing native localRingHom, with both actual objects retained
as commutative algebras over their original base. -/
def commAlgPrimeComapMap {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (p : Ideal S) [p.IsPrime] :
    commAlgPrimeComapLocalization R S f p →+* commAlgPrimeLocalization S p :=
  primeLocalizationComapMap f p

/-- The existing native coefficient square for the actual prime-comap map. -/
theorem commAlgPrimeComapMap_comp_coefficient {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (p : Ideal S) [p.IsPrime] :
    (commAlgPrimeComapMap R S f p).comp (commAlgPrimeComapCoefficientMap R S f p) =
      (commAlgPrimeCoefficientMap S p).comp f :=
  primeLocalizationComapMap_comp_coefficient f p

/-- The existing native prime coefficient map is injective in a domain,
with its target retained as the computed commutative algebra object. -/
theorem commAlgPrimeCoefficientMap_injective {A : Type u} [CommRing A]
    (S : CommAlgCat.{v} A) [IsDomain S] (p : Ideal S) [p.IsPrime] :
    Function.Injective (commAlgPrimeCoefficientMap S p).toFun :=
  nativePrimeCoefficientMap_injective S p

/-- The actual contracted-prime condition makes the coefficient image a
unit in the native prime localization, before any principal source appears. -/
theorem commAlgPrimeCoefficientMap_comp_isUnit {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (d : R) (p : Ideal S) [p.IsPrime]
    (h : d ∉ commAlgContractionIdeal R S f p) :
    IsUnit (((commAlgPrimeCoefficientMap S p).comp f).toFun d) :=
  primeLocalizationCoefficientMap_comp_isUnit f d p h

/-- The native principal lift into an already constructed target algebra.
Its sole unit input concerns the actual supplied coefficient map. -/
def commAlgPrincipalLift {A : Type u} [CommRing A]
    (R T : CommAlgCat.{v} A) (f : R →+* T) (d : R)
    (h : IsUnit (f.toFun d)) : commAlgPrincipalLocalization R d →+* T := by
  have : IsLocalization.Away d (localizationAwayCommAlgCat R R d) :=
    localizationAwayCommAlgCat_isLocalization R d
  exact IsLocalization.Away.lift (S := localizationAwayCommAlgCat R R d) d (g := f) h

/-- The native lift has precisely the prescribed coefficient map. -/
theorem commAlgPrincipalLift_comp_coefficient {A : Type u} [CommRing A]
    (R T : CommAlgCat.{v} A) (f : R →+* T) (d : R) (h : IsUnit (f.toFun d)) :
    (commAlgPrincipalLift R T f d h).comp (commAlgPrincipalCoefficientMap R d) = f := by
  have : IsLocalization.Away d (localizationAwayCommAlgCat R R d) :=
    localizationAwayCommAlgCat_isLocalization R d
  exact IsLocalization.Away.lift_comp (S := localizationAwayCommAlgCat R R d) d (g := f) h

/-- Injectivity of the coefficient map supplies injectivity of this actual
native lift, by the single existing principal-localization argument. -/
theorem commAlgPrincipalLift_injective {A : Type u} [CommRing A]
    (R T : CommAlgCat.{v} A) (f : R →+* T) (d : R) (h : IsUnit (f.toFun d))
    (hf : Function.Injective f.toFun) :
    Function.Injective (commAlgPrincipalLift R T f d h).toFun := by
  have hcoeff : Function.Injective
      ((commAlgPrincipalLift R T f d h).comp (commAlgPrincipalCoefficientMap R d)).toFun := by
    rw [commAlgPrincipalLift_comp_coefficient R T f d h]
    exact hf
  exact principalLocalization_injective_of_coefficient_injective d
    (commAlgPrincipalLift R T f d h) hcoeff

/-- Factoring the coefficient map through the native prime coefficient
does not change the previously constructed principal-to-prime map. -/
theorem commAlgPrincipalLift_eq_toPrime {A : Type u} [CommRing A]
    (R S : CommAlgCat.{v} A) (f : R →+* S) (d : R) (p : Ideal S) [p.IsPrime]
    (h : d ∉ commAlgContractionIdeal R S f p) :
    commAlgPrincipalLift R (commAlgPrimeLocalization S p)
        ((commAlgPrimeCoefficientMap S p).comp f) d
        (commAlgPrimeCoefficientMap_comp_isUnit R S f d p h) =
      commAlgPrincipalToPrimeMap R S f d p h := by
  apply commAlgPrincipalRingHom_ext R d
  exact (commAlgPrincipalLift_comp_coefficient R (commAlgPrimeLocalization S p)
    ((commAlgPrimeCoefficientMap S p).comp f) d
    (commAlgPrimeCoefficientMap_comp_isUnit R S f d p h)).trans
      (commAlgPrincipalToPrimeMap_comp_coefficient R S f d p h).symm

end SchemeTheory
