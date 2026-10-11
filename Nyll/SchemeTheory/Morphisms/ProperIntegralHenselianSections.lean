/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianIntegralDomainLocal
import Nyll.SchemeTheory.RingTheory.HenselianLocalRing_of_isIntegral_of_isLocalRing
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.RingHom.Integral

/-!
# The actual section ring of a proper integral henselian family

Universal closedness makes the actual global-section algebra integral over
the base. When the total space is integral and the base is henselian local,
the section ring is therefore henselian local, without a finiteness or
Noetherian hypothesis. Its unique closed point lies over the base closed
point, and it is the only point doing so. Consequently the original closed
fiber and the closed fiber of the canonical affinization have exactly the
same underlying subset of the total space.

This supplies the integral henselian base in the Stein-factorization route
to Stacks 0A0B. Connectedness of the affinization fibers is a separate
geometric assertion and is not assumed or claimed here.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

private def sectionRingMap {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : R →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

private lemma sectionRingMap_isIntegral {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] :
    (sectionRingMap f).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed f

private lemma toSpecΓ_specMap_sectionRingMap {R : Type u} [CommRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionRingMap f)) = f := by
  change X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop) = f
  rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality,
    Category.assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- The actual ring of global sections of an integral universally closed
scheme over a henselian local ring is henselian local. In particular this
applies to proper integral schemes without any Noetherian assumption. -/
theorem henselianLocalRing_globalSections_of_universallyClosed
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] :
    HenselianLocalRing Γ(X, ⊤) := by
  let : Algebra R Γ(X, ⊤) := (sectionRingMap f).toAlgebra
  have : Algebra.IsIntegral R Γ(X, ⊤) :=
    (algebraMap_isIntegral_iff).mp (sectionRingMap_isIntegral f)
  have : IsLocalRing Γ(X, ⊤) :=
    SchemeTheory.isLocalRing_of_integral_domain_henselian R Γ(X, ⊤)
  exact HenselianLocalRing.of_isIntegral_of_isLocalRing (R := R)

/-- For an integral universally closed scheme over a henselian local ring,
the original closed fiber is exactly the closed fiber of its canonical
affinization. The local structure on the actual section ring is supplied
by its integrality; it is not an additional input. -/
theorem closedFiber_eq_affinization_closedFiber
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f] :
    let : HenselianLocalRing Γ(X, ⊤) :=
      henselianLocalRing_globalSections_of_universallyClosed f
    f ⁻¹' {IsLocalRing.closedPoint R} =
      X.toSpecΓ ⁻¹' {IsLocalRing.closedPoint Γ(X, ⊤)} := by
  intro
  let : Algebra R Γ(X, ⊤) := (sectionRingMap f).toAlgebra
  have : Algebra.IsIntegral R Γ(X, ⊤) :=
    (algebraMap_isIntegral_iff).mp (sectionRingMap_isIntegral f)
  have hClosed (p : PrimeSpectrum Γ(X, ⊤)) :
      PrimeSpectrum.comap (sectionRingMap f) p = IsLocalRing.closedPoint R ↔
        p = IsLocalRing.closedPoint Γ(X, ⊤) := by
    constructor
    · intro hp
      have hpIdeal : p.asIdeal.comap (algebraMap R Γ(X, ⊤)) =
          IsLocalRing.maximalIdeal R := congrArg PrimeSpectrum.asIdeal hp
      have : p.asIdeal.IsPrime := p.isPrime
      have hMax : (p.asIdeal.comap (algebraMap R Γ(X, ⊤))).IsMaximal := by
        rw [hpIdeal]
        infer_instance
      have hpMax : p.asIdeal.IsMaximal :=
        Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) p.asIdeal hMax
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hpMax)
    · rintro rfl
      have hMax : ((IsLocalRing.maximalIdeal Γ(X, ⊤)).comap
          (algebraMap R Γ(X, ⊤))).IsMaximal :=
        Ideal.isMaximal_under_of_isIntegral_of_isMaximal
          (R := R) (IsLocalRing.maximalIdeal Γ(X, ⊤))
      exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hMax)
  ext x
  change f x = IsLocalRing.closedPoint R ↔
    X.toSpecΓ x = IsLocalRing.closedPoint Γ(X, ⊤)
  rw [← toSpecΓ_specMap_sectionRingMap f, Scheme.Hom.comp_apply, Spec.map_apply]
  exact hClosed (X.toSpecΓ x)

end AlgebraicGeometry
