/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.IdealCyclotomicBaseResidue

/-!
# Cyclotomic inversion from a divisorial residue field

For a discrete valuation base, the residue field is the function field of the
corresponding prime divisor.  This file identifies that field with the
intrinsic decomposition residue field of a prime in a finite Galois
normalization, and feeds geometric integrality of the divisorial residue
field into finite-level cyclotomic inversion.
-/

noncomputable section

universe uB uK uL

namespace TameAbhyankar.SGA1

open CategoryTheory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

private theorem geometricallyIntegral_specMap_transport_dvrResidueEquiv
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

/-- A prime above the maximal ideal of a discrete valuation base is nonzero.
The torsion-free algebra instance is constructed from the specified integral
closure rather than exposed as an additional hypothesis. -/
theorem dvrNormalizationPrime_ne_bot
    {A : Type uL} {B : Type uB} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [Algebra K L] [Algebra A B] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (P : Ideal B) [P.LiesOver (IsLocalRing.maximalIdeal A)] : P ≠ ⊥ := by
  let : Module.IsTorsionFree A L :=
    Module.IsTorsionFree.trans_faithfulSMul A K L
  have hAL : Function.Injective (algebraMap A L) := by
    intro x y hxy
    apply IsFractionRing.injective A K
    apply (algebraMap K L).injective
    simpa only [IsScalarTower.algebraMap_apply A K L] using hxy
  have hAB : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply hAL
    rw [IsScalarTower.algebraMap_apply A B L,
      IsScalarTower.algebraMap_apply A B L, hxy]
  let : Nontrivial B :=
    hAB.nontrivial
  let : Module.IsTorsionFree A B :=
    IsIntegralClosure.isTorsionFree A L
  exact Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field A) P

/-- The residue field of a discrete valuation base is canonically the
intrinsic decomposition residue field at a prime of a finite Galois
normalization.  The nonzero-prime input is produced from the DVR maximal
ideal and the lies-over relation. -/
def dvrResidueEquivDecompositionResidueField
    {A : Type uL} {B : Type uB} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal B) [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal A)]
    [CharZero (IsLocalRing.ResidueField A)] :
    let hP : P ≠ ⊥ := dvrNormalizationPrime_ne_bot
      (A := A) (K := K) (L := L) P
    IsLocalRing.ResidueField A ≃+*
      decompositionResidueField K
        (idealLocalizationValuationSubring B L P hP) := by
  let p := IsLocalRing.maximalIdeal A
  let hP : P ≠ ⊥ := dvrNormalizationPrime_ne_bot
    (A := A) (K := K) (L := L) P
  have hp : normalizationIdealBasePrime (A := A) P = p :=
    (P.over_def p).symm
  letI : (normalizationIdealBasePrime (A := A) P).IsMaximal :=
    normalizationIdealBasePrime_isMaximal
      (A := A) (B := B) (L := L) P
  let q : IsLocalRing.ResidueField A ≃+*
      A ⧸ normalizationIdealBasePrime (A := A) P :=
    Ideal.quotEquivOfEq hp.symm
  letI : CharZero (A ⧸ normalizationIdealBasePrime (A := A) P) :=
    q.symm.toRingHom.charZero
  exact q.trans
    (normalizationBaseResidueEquivDecompositionResidueField
      (A := A) (B := B) (K := K) (L := L) (P := P) (hP := hP))

/-- Geometric integrality of the residue field of a discrete valuation base
over a rational field makes every normalization-ideal inertia element
conjugate to its inverse in the ambient finite Galois group. -/
theorem idealInertia_isConj_inv_of_geometricallyIntegral_dvrResidue_of_ratEquiv
    (k : Type uL) [Field k] (e : k ≃+* ℚ)
    {A : Type uL} {B : Type uB} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDedekindDomain B]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal B) [P.IsMaximal]
    [P.LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra k (IsLocalRing.ResidueField A)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (IsLocalRing.ResidueField A))))) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ sigma : P.toAddSubgroup.inertia Gal(L/K),
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : P.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  let p := IsLocalRing.maximalIdeal A
  have hP : P ≠ ⊥ := dvrNormalizationPrime_ne_bot
    (A := A) (K := K) (L := L) P
  have hp : normalizationIdealBasePrime (A := A) P = p :=
    (P.over_def p).symm
  let : (normalizationIdealBasePrime (A := A) P).IsMaximal :=
    normalizationIdealBasePrime_isMaximal
      (A := A) (B := B) (L := L) P
  let q : IsLocalRing.ResidueField A ≃+*
      A ⧸ normalizationIdealBasePrime (A := A) P :=
    Ideal.quotEquivOfEq hp.symm
  let : Algebra k (A ⧸ normalizationIdealBasePrime (A := A) P) :=
    (q.toRingHom.comp
      (algebraMap k (IsLocalRing.ResidueField A))).toAlgebra
  have hgeoBase : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k
          (A ⧸ normalizationIdealBasePrime (A := A) P)))) :=
    geometricallyIntegral_specMap_transport_dvrResidueEquiv
      (R := IsLocalRing.ResidueField A)
      (S := A ⧸ normalizationIdealBasePrime (A := A) P) q hgeo
  exact
    idealInertia_isConj_inv_of_geometricallyIntegral_basePrimeResidue_of_ratEquiv
      k e (A := A) (B := B) (K := K) (L := L) P hP hgeoBase

/-- The normalization-specialized DVR endpoint.  Fraction-field and
Dedekind instances for the integral closure, as well as maximality of the
chosen prime, are produced internally. -/
theorem
    idealInertia_isConj_inv_of_geometricallyIntegral_dvrNormalizationResidue_of_ratEquiv
    (k : Type uL) [Field k] (e : k ≃+* ℚ)
    {A : Type uL} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal (integralClosure A L)) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra k (IsLocalRing.ResidueField A)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (IsLocalRing.ResidueField A))))) :
    letI := IsIntegralClosure.MulSemiringAction
      A K L (integralClosure A L)
    ∀ sigma : P.toAddSubgroup.inertia Gal(L/K),
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : P.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain A K L B
  let : P.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal P
      (IsLocalRing.maximalIdeal A)
  let := IsIntegralClosure.MulSemiringAction A K L B
  exact
    idealInertia_isConj_inv_of_geometricallyIntegral_dvrResidue_of_ratEquiv
      k e (A := A) (B := B) (K := K) (L := L) P hgeo

end TameAbhyankar.SGA1

end
