/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.CyclotomicRestriction

/-!
# Cyclotomic inversion in finite-level inertia

The normal residue extension attached to a decomposition group is embedded in
a genuine separable closure.  Cyclotomic inversion restricts to that normal
extension and the residue exact sequence lifts it back to the decomposition
group.  The selected residue field itself need not be a separable closure.
-/

noncomputable section


universe u v

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

/-- Geometric integrality over a rational base produces one decomposition
element which conjugates every finite inertia element to its inverse.

The selected residue field is only used as its actual normal separable
extension of the decomposition residue field.  In particular, it is not
assumed to be a separable closure. -/
theorem
    exists_inertiaConjugate_eq_inv_of_geometricallyIntegral_residueExtension_of_ratEquiv
    (k : Type v) [Field k] (e : k ≃+* ℚ)
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [Finite (inertiaGroup K V)]
    [Algebra k (decompositionResidueField K V)]
    [Algebra k (selectedResidueField V)]
    [IsScalarTower k (decompositionResidueField K V)
      (selectedResidueField V)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (decompositionResidueField K V))))) :
    ∃ g : decompositionGroup K V,
      ∀ sigma : inertiaGroup K V,
        inertiaConjugate K V g sigma = sigma⁻¹ := by
  let F := decompositionResidueField K V
  let E := selectedResidueField V
  let Omega := SeparableClosure F
  let : CharZero k := e.toRingHom.charZero
  let : CharZero F :=
    charZero_of_injective_algebraMap (algebraMap k F).injective
  let : PerfectField F := PerfectField.ofCharZero
  let : Algebra.IsSeparable F E := inferInstance
  let : CharZero E :=
    charZero_of_injective_algebraMap (algebraMap F E).injective
  let : Algebra k Omega :=
    ((algebraMap F Omega).comp (algebraMap k F)).toAlgebra
  let : IsScalarTower k F Omega :=
    IsScalarTower.of_algebraMap_eq fun x => rfl
  let : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k F))) := hgeo
  have hdisjoint : (separableClosure k Omega).LinearDisjoint F :=
    EtaleFundamentalGroups.separableClosure_linearDisjoint_of_geometricallyIntegral
  obtain ⟨tau, htau⟩ :=
    (open _root_.EtaleFundamentalGroups in
      exists_normalAlgEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint_of_ratEquiv
        (F := F) (E := E) (Omega := Omega) e hdisjoint)
  obtain ⟨g, hg, hresidue⟩ :=
    exists_galoisAutomorphism_stabilizing_of_residueAutomorphism K V tau
  let g' : decompositionGroup K V := ⟨g, hg⟩
  refine ⟨g', ?_⟩
  intro sigma
  apply inertiaConjugate_eq_inv_of_torsion_residue_inversion K V g'
  intro z hz
  have haction :
      residueAction K V g' (z : selectedResidueField V) =
        tau (z : selectedResidueField V) := by
    exact DFunLike.congr_fun hresidue (z : selectedResidueField V)
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change residueAction K V g' (z : selectedResidueField V) =
    (z : selectedResidueField V)⁻¹
  rw [haction]
  have hinv := congrArg Units.val (htau z hz)
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val] at hinv
  exact hinv

/-- Under the same finite-level residue input, every inertia element is
conjugate to its inverse inside the decomposition group, without identifying
the selected residue field with a separable closure. -/
theorem
    inertia_isConj_inv_of_geometricallyIntegral_residueExtension_of_ratEquiv
    (k : Type v) [Field k] (e : k ≃+* ℚ)
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [Finite (inertiaGroup K V)]
    [Algebra k (decompositionResidueField K V)]
    [Algebra k (selectedResidueField V)]
    [IsScalarTower k (decompositionResidueField K V)
      (selectedResidueField V)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (decompositionResidueField K V))))) :
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  obtain ⟨g, hg⟩ :=
    exists_inertiaConjugate_eq_inv_of_geometricallyIntegral_residueExtension_of_ratEquiv
      k e K V hgeo
  intro sigma
  refine isConj_iff.mpr ⟨g, ?_⟩
  exact congrArg Subtype.val (hg sigma)

section IntegerBase

local instance : IsDomain (ULift.{v} ℤ) :=
  (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

private abbrev integerGenericResidueField : Type v :=
  AlgebraicGeometry.Scheme.residueField
    (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{v} ℤ)))
    (_root_.genericPoint
      (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{v} ℤ))))

/-- The generic residue field of the integer base supplies finite-level
cyclotomic inversion without requiring the selected residue field to be a
separable closure. -/
theorem
    inertia_isConj_inv_of_geometricallyIntegral_residueExtension_over_integers
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [Finite (inertiaGroup K V)]
    [Algebra integerGenericResidueField (decompositionResidueField K V)]
    [Algebra integerGenericResidueField (selectedResidueField V)]
    [IsScalarTower integerGenericResidueField
      (decompositionResidueField K V) (selectedResidueField V)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap integerGenericResidueField
          (decompositionResidueField K V))))) :
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  let e : integerGenericResidueField ≃+* ℚ :=
    AlgebraicGeometry.specULiftZGenericResidueFieldEquivQ
  exact
    inertia_isConj_inv_of_geometricallyIntegral_residueExtension_of_ratEquiv
      integerGenericResidueField e K V hgeo

end IntegerBase

end TameAbhyankar.SGA1

end
