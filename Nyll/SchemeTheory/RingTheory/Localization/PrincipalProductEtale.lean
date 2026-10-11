/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Nyll.SchemeTheory.RingTheory.Localization.AwayAlgebra
import Nyll.SchemeTheory.RingTheory.Localization.AwayToPrime
import Nyll.SchemeTheory.RingTheory.Localization.CommAlgPrincipal
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Smooth
import Mathlib.RingTheory.RingHom.Unramified

/-!
# Etaleness of the actual principal-product transition

The transition is the existing native principal map from R_f to R_(f*d).
Its etaleness is proved through the actual second principal localization
of R_f. The product-localization equivalence and its coefficient equation
are established before introducing another coefficient base.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- Etale ring homomorphisms compose without identifying the universes of
the coefficient, intermediate, and target rings. -/
theorem ringHom_etale_comp {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (g : S →+* T) (hf : f.Etale) (hg : g.Etale) :
    (g.comp f).Etale := by
  obtain ⟨hfU, hfS⟩ := (RingHom.etale_iff_formallyUnramified_and_smooth f).mp hf
  obtain ⟨hgU, hgS⟩ := (RingHom.etale_iff_formallyUnramified_and_smooth g).mp hg
  exact (RingHom.etale_iff_formallyUnramified_and_smooth (g.comp f)).mpr
    ⟨RingHom.FormallyUnramified.comp (f := f) (g := g) hfU hgU,
      RingHom.Smooth.comp (f := f) (g := g) hfS hgS⟩

private def nativePrincipalAlgebra (R : Type u) [CommRing R] (f : R) :
    CommAlgCat.{u} R :=
  localizationAwayCommAlgCat R R f

private theorem nativePrincipalAlgebra_isLocalization
    (R : Type u) [CommRing R] (f : R) :
    IsLocalization.Away f (nativePrincipalAlgebra R f) :=
  localizationAwayCommAlgCat_isLocalization R f

private def nativePrincipalCoefficient (R : Type u) [CommRing R] (f : R) :
    R →+* nativePrincipalAlgebra R f :=
  principalLocalizationCoefficientMap R f

/-- The literal second localization with its existing native R-action. -/
private def nativePrincipalProductAlgebra (R : Type u) [CommRing R] (f d : R) :
    CommAlgCat.{u} R :=
  commAlgPrincipalLocalization (nativePrincipalAlgebra R f)
    ((nativePrincipalCoefficient R f).toFun d)

/-- The two native presentations have the same ring and the same original
R-action. Only that already constructed action is supplied to the native
two-stage localization theorem. -/
private theorem nativePrincipalProductAlgebra_isLocalization
    (R : Type u) [CommRing R] (f d : R) :
    IsLocalization.Away (f * d) (nativePrincipalProductAlgebra R f d) := by
  let S : CommAlgCat.{u} R := nativePrincipalAlgebra R f
  let T : CommAlgCat.{u} S := nativePrincipalAlgebra S
    ((nativePrincipalCoefficient R f).toFun d)
  let : Algebra R T := (nativePrincipalProductAlgebra R f d).algebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.Away f S := nativePrincipalAlgebra_isLocalization R f
  have : IsLocalization.Away (algebraMap R S d) T :=
    nativePrincipalAlgebra_isLocalization S ((nativePrincipalCoefficient R f).toFun d)
  exact IsLocalization.Away.mul' (S := S) T f d

private def nativePrincipalProductAlgEquiv (R : Type u) [CommRing R] (f d : R) :
    nativePrincipalProductAlgebra R f d ≃ₐ[R] nativePrincipalAlgebra R (f * d) := by
  have : IsLocalization.Away (f * d) (nativePrincipalProductAlgebra R f d) :=
    nativePrincipalProductAlgebra_isLocalization R f d
  have : IsLocalization.Away (f * d) (nativePrincipalAlgebra R (f * d)) :=
    nativePrincipalAlgebra_isLocalization R (f * d)
  exact IsLocalization.algEquiv (Submonoid.powers (f * d))
    (nativePrincipalProductAlgebra R f d) (nativePrincipalAlgebra R (f * d))

private def nativePrincipalProductEquiv (R : Type u) [CommRing R] (f d : R) :
    nativePrincipalProductAlgebra R f d ≃+* nativePrincipalAlgebra R (f * d) :=
  (nativePrincipalProductAlgEquiv R f d).toRingEquiv

private def nativePrincipalProductCoefficient (R : Type u) [CommRing R] (f d : R) :
    nativePrincipalAlgebra R f →+* nativePrincipalProductAlgebra R f d :=
  commAlgPrincipalCoefficientMap (nativePrincipalAlgebra R f)
    ((nativePrincipalCoefficient R f).toFun d)

private theorem nativePrincipalProductCoefficient_comp_base
    (R : Type u) [CommRing R] (f d : R) :
    (nativePrincipalProductCoefficient R f d).comp (nativePrincipalCoefficient R f) =
      commAlgCoefficientMap (nativePrincipalProductAlgebra R f d) :=
  commAlgPrincipalCoefficientMap_comp_base (nativePrincipalAlgebra R f)
    ((nativePrincipalCoefficient R f).toFun d)

private theorem nativePrincipalProductEquiv_comp_base
    (R : Type u) [CommRing R] (f d : R) :
    (nativePrincipalProductEquiv R f d).toRingHom.comp
        (commAlgCoefficientMap (nativePrincipalProductAlgebra R f d)) =
      nativePrincipalCoefficient R (f * d) :=
  (nativePrincipalProductAlgEquiv R f d).toAlgHom.comp_algebraMap

private theorem nativePrincipalProductCoefficient_etale
    (R : Type u) [CommRing R] (f d : R) :
    (nativePrincipalProductCoefficient R f d).Etale := by
  let S : CommAlgCat.{u} R := nativePrincipalAlgebra R f
  let t : S := (nativePrincipalCoefficient R f).toFun d
  have : IsLocalization.Away t (nativePrincipalAlgebra S t) :=
    nativePrincipalAlgebra_isLocalization S t
  change (algebraMap S (nativePrincipalAlgebra S t)).Etale
  exact RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway t)

/-- The actual constructed native transition to the product denominator. -/
def commAlgPrincipalProductMap {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (f d : R) :
    commAlgPrincipalLocalization R f →+* commAlgPrincipalLocalization R (f * d) :=
  commAlgPrincipalTransitionMap R R (RingHom.id R) f (f * d) (dvd_mul_right f d)

/-- The product transition retains the original native coefficient map. -/
theorem commAlgPrincipalProductMap_comp_coefficient {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (f d : R) :
    (commAlgPrincipalProductMap R f d).comp (commAlgPrincipalCoefficientMap R f) =
      commAlgPrincipalCoefficientMap R (f * d) := by
  exact (commAlgPrincipalTransitionMap_comp_coefficient R R (RingHom.id R)
    f (f * d) (dvd_mul_right f d)).trans
      (RingHom.comp_id (commAlgPrincipalCoefficientMap R (f * d)))

private theorem nativePrincipalProductMap_eq
    (R : Type u) [CommRing R] (f d : R) :
    commAlgPrincipalProductMap (CommAlgCat.of R R) f d =
      (nativePrincipalProductEquiv R f d).toRingHom.comp
        (nativePrincipalProductCoefficient R f d) := by
  let j : nativePrincipalAlgebra R f →+* nativePrincipalAlgebra R (f * d) :=
    commAlgPrincipalProductMap (CommAlgCat.of R R) f d
  let c : R →+* nativePrincipalAlgebra R f := nativePrincipalCoefficient R f
  let b : R →+* nativePrincipalAlgebra R (f * d) := nativePrincipalCoefficient R (f * d)
  let a : R →+* nativePrincipalProductAlgebra R f d :=
    commAlgCoefficientMap (nativePrincipalProductAlgebra R f d)
  let e : nativePrincipalProductAlgebra R f d →+* nativePrincipalAlgebra R (f * d) :=
    (nativePrincipalProductEquiv R f d).toRingHom
  let t : nativePrincipalAlgebra R f →+* nativePrincipalProductAlgebra R f d :=
    nativePrincipalProductCoefficient R f d
  have hleft : j.comp c = b :=
    commAlgPrincipalProductMap_comp_coefficient (CommAlgCat.of R R) f d
  have hright : e.comp a = b := nativePrincipalProductEquiv_comp_base R f d
  have hmiddle : t.comp c = a := nativePrincipalProductCoefficient_comp_base R f d
  change j = e.comp t
  apply commAlgPrincipalRingHom_ext (CommAlgCat.of R R) f
  change j.comp c = (e.comp t).comp c
  exact hleft.trans (hright.symm.trans
    ((congrArg (fun k : R →+* nativePrincipalProductAlgebra R f d => e.comp k)
      hmiddle.symm).trans (RingHom.comp_assoc c t e).symm))

private theorem nativePrincipalProductMap_etale
    (R : Type u) [CommRing R] (f d : R) :
    (commAlgPrincipalProductMap (CommAlgCat.of R R) f d).Etale := by
  rw [nativePrincipalProductMap_eq R f d]
  apply RingHom.Etale.stableUnderComposition
  · exact nativePrincipalProductCoefficient_etale R f d
  · exact RingHom.Etale.of_bijective (nativePrincipalProductEquiv R f d).bijective

/-- The native principal-product transition is etale. The proof uses the
original R-only nested-localization equivalence, with no new A-action. -/
theorem commAlgPrincipalProductMap_etale {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (f d : R) :
    (commAlgPrincipalProductMap R f d).Etale :=
  nativePrincipalProductMap_etale R f d

/-- The product transition preserves the original base coefficient map.
This square follows from the native localization coefficient equations. -/
theorem commAlgPrincipalProductMap_comp_base {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (f d : R) :
    (commAlgPrincipalProductMap R f d).comp
        (commAlgCoefficientMap (commAlgPrincipalLocalization R f)) =
      commAlgCoefficientMap (commAlgPrincipalLocalization R (f * d)) := by
  rw [← commAlgPrincipalCoefficientMap_comp_base R f,
    ← RingHom.comp_assoc,
    commAlgPrincipalProductMap_comp_coefficient R f d,
    commAlgPrincipalCoefficientMap_comp_base R (f * d)]

/-- Refining a proved principal etale neighborhood by a product preserves
etaleness of its actual original-base coefficient map. The heterogeneous
ring-map composition theorems retain independent base and carrier universes. -/
theorem commAlgPrincipalProductCoefficient_etale {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (f d : R)
    (hf : (commAlgCoefficientMap (commAlgPrincipalLocalization R f)).Etale) :
    (commAlgCoefficientMap (commAlgPrincipalLocalization R (f * d))).Etale := by
  rw [← commAlgPrincipalProductMap_comp_base R f d]
  exact ringHom_etale_comp
    (commAlgCoefficientMap (commAlgPrincipalLocalization R f))
    (commAlgPrincipalProductMap R f d) hf (commAlgPrincipalProductMap_etale R f d)

/-- The product refinement is etale for the original stored A-action.
The input is the already proved etaleness of the chosen principal stage. -/
theorem commAlgPrincipalProduct_etale {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (f d : R)
    (hf : Algebra.Etale A (commAlgPrincipalLocalization R f)) :
    Algebra.Etale A (commAlgPrincipalLocalization R (f * d)) := by
  apply (RingHom.etale_algebraMap
    (R := A) (S := commAlgPrincipalLocalization R (f * d))).mp
  exact commAlgPrincipalProductCoefficient_etale R f d
    ((RingHom.etale_algebraMap
      (R := A) (S := commAlgPrincipalLocalization R f)).mpr hf)

end SchemeTheory
