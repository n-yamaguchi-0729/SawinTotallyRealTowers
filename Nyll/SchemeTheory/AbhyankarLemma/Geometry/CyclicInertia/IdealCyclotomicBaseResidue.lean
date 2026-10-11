/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.IdealCyclotomicInversion
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealResidueComparison

/-!
# Cyclotomic inversion from a normalization base residue field

The residue field of a base prime is canonically identified with the
intrinsic decomposition residue field after localization.  Consequently,
geometric integrality stated on the base-prime residue field supplies the
finite-level cyclotomic conjugation theorem for normalization-ideal inertia.
-/

noncomputable section


universe uB uK uL

namespace TameAbhyankar.SGA1

open CategoryTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

private theorem geometricallyIntegral_specMap_transport_ringEquiv
    {k R S : Type uL} [Field k] [Field R] [Field S]
    [Algebra k R] (e : R ≃+* S)
    (h : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k R)))) :
    letI : Algebra k S :=
      (e.toRingHom.comp (algebraMap k R)).toAlgebra
    AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k S))) := by
  let : Algebra k S :=
    (e.toRingHom.comp (algebraMap k R)).toAlgebra
  let i : AlgebraicGeometry.Spec (CommRingCat.of S) ≅
      AlgebraicGeometry.Spec (CommRingCat.of R) :=
    AlgebraicGeometry.Scheme.Spec.mapIso e.toCommRingCatIso.op
  have hi : AlgebraicGeometry.GeometricallyIntegral
      (i.hom ≫ AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k R))) := by
    let : MorphismProperty.RespectsIso
        (@AlgebraicGeometry.GeometricallyIntegral :
          MorphismProperty AlgebraicGeometry.Scheme.{uL}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
        (P := (@AlgebraicGeometry.GeometricallyIntegral :
          MorphismProperty AlgebraicGeometry.Scheme.{uL}))
    exact (MorphismProperty.cancel_left_of_respectsIso
      (C := AlgebraicGeometry.Scheme.{uL})
      (P := (@AlgebraicGeometry.GeometricallyIntegral :
        MorphismProperty AlgebraicGeometry.Scheme.{uL}))
      i.hom
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k R)))).mpr h
  have hmap : CommRingCat.ofHom (algebraMap k R) ≫
      e.toCommRingCatIso.hom.op.unop =
      CommRingCat.ofHom (algebraMap k S) := by
    ext x
    rfl
  simpa only [i, Functor.mapIso_hom, Iso.op_hom,
    AlgebraicGeometry.Scheme.Spec_map,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hmap]
    using hi

/-- Geometric integrality on the residue field of the base prime makes every
normalization-ideal inertia element conjugate to its inverse in the ambient
finite Galois group. -/
theorem
    idealInertia_isConj_inv_of_geometricallyIntegral_basePrimeResidue_of_ratEquiv
    (k : Type uL) [Field k] (e : k ≃+* ℚ)
    {A : Type uL} {B : Type uB} {K : Type uK} {L : Type uL}
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsDedekindDomain B]
    [IsIntegrallyClosed A]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥)
    [Algebra k (A ⧸ normalizationIdealBasePrime (A := A) P)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k
          (A ⧸ normalizationIdealBasePrime (A := A) P))))) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ sigma : P.toAddSubgroup.inertia Gal(L/K),
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : P.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  let p := normalizationIdealBasePrime (A := A) P
  let V := idealLocalizationValuationSubring B L P hP
  let F := decompositionResidueField K V
  let E := selectedResidueField V
  let : p.IsMaximal := normalizationIdealBasePrime_isMaximal
    (A := A) (B := B) (L := L) P
  let : CharZero k := e.toRingHom.charZero
  let : CharZero (A ⧸ p) :=
    charZero_of_injective_algebraMap
      (algebraMap k (A ⧸ p)).injective
  let q : A ⧸ p ≃+* F :=
    normalizationBaseResidueEquivDecompositionResidueField
      (A := A) (B := B) (K := K) (L := L) (P := P) (hP := hP)
  let : Algebra k F :=
    (q.toRingHom.comp (algebraMap k (A ⧸ p))).toAlgebra
  let : Algebra k E :=
    ((algebraMap F E).comp (algebraMap k F)).toAlgebra
  let : IsScalarTower k F E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hgeoF : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k F))) :=
    geometricallyIntegral_specMap_transport_ringEquiv q hgeo
  exact
    idealInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
      k e (A := A) (B := B) (K := K) (L := L) P hP hgeoF

end TameAbhyankar.SGA1

end
