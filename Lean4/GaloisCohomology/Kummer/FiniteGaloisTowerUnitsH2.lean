/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteGaloisUnitsCohomologyTransport
import GaloisCohomology.Kummer.UnitsCohomologyCongr
import GaloisCohomology.Kummer.UnitsCohomologyRestrictScalars
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false

/-!
# Unit H² in an arbitrary finite Galois tower

The actual restriction homomorphisms and inclusion of units define the
inflation and restriction maps without representing the lower field as a
subtype of the upper field.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K F N : Type) [Field K] [Field F] [Field N]
  [Algebra K F] [Algebra F N] [Algebra K N] [IsScalarTower K F N]

/-- Inclusion of units in a normal field tower, equivariant for restriction. -/
def finiteGaloisTowerUnitsInflationRepHom [Normal K F] :
    Rep.res (AlgEquiv.restrictNormalHom F) (Rep.ofAlgebraAutOnUnits K F) ⟶
      Rep.ofAlgebraAutOnUnits K N := by
  apply Rep.ofHom
  refine ⟨(Units.map (algebraMap F N).toMonoidHom).toAdditive.toIntLinearMap, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  apply Units.ext
  exact σ.restrictNormal_commutes F ((show Additive Fˣ from a).toMul : F)

/-- Inflation induced by restricting automorphisms and including field units. -/
def finiteGaloisTowerUnitsH2Inflation [Normal K F] :
    groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits K N) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom F)
    (finiteGaloisTowerUnitsInflationRepHom K F N) 2

/-- Relative restriction leaves upper-field units unchanged. -/
def finiteGaloisTowerUnitsRestrictionRepHom :
    Rep.res (AlgEquiv.restrictScalarsHom K) (Rep.ofAlgebraAutOnUnits K N) ⟶
      Rep.ofAlgebraAutOnUnits F N :=
  Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩

/-- Restriction to the relative Galois group, with identical unit coefficients. -/
def finiteGaloisTowerUnitsH2Restriction :
    groupCohomology (Rep.ofAlgebraAutOnUnits K N) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits F N) 2 :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (finiteGaloisTowerUnitsRestrictionRepHom K F N) 2

private theorem restriction_intermediateField (E : IntermediateField K N) :
    finiteGaloisUnitsH2Restriction K N E =
      finiteGaloisTowerUnitsH2Restriction K E N := by
  let ψ : Rep.res E.fixingSubgroupEquiv.symm.toMonoidHom
      (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N)) ⟶
      Rep.ofAlgebraAutOnUnits E N := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩
  change groupCohomology.map E.fixingSubgroup.subtype
      (𝟙 (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N))) 2 ≫
    groupCohomology.map E.fixingSubgroupEquiv.symm.toMonoidHom ψ 2 =
      finiteGaloisTowerUnitsH2Restriction K E N
  refine (groupCohomology.map_comp
    (A := Rep.ofAlgebraAutOnUnits K N)
    (B := Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N))
    (C := Rep.ofAlgebraAutOnUnits E N) E.fixingSubgroup.subtype
    E.fixingSubgroupEquiv.symm.toMonoidHom
    (𝟙 (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N))) ψ 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · apply LinearMap.ext
    intro a
    rfl

private theorem fieldRange_inflation [Normal K F]
    [Normal K (IsScalarTower.toAlgHom K F N).fieldRange] :
    (unitsCohomologyCongrTop K F (IsScalarTower.toAlgHom K F N).fieldRange
      (IsScalarTower.toAlgHom K F N).equivFieldRange 2).hom ≫
        finiteGaloisUnitsH2Inflation K N (IsScalarTower.toAlgHom K F N).fieldRange =
      finiteGaloisTowerUnitsH2Inflation K F N := by
  let i : F →ₐ[K] N := IsScalarTower.toAlgHom K F N
  let E : IntermediateField K N := i.fieldRange
  let e : F ≃ₐ[K] E := i.equivFieldRange
  let φ : Rep.res (AlgEquiv.autCongr e).symm.toMonoidHom
      (Rep.ofAlgebraAutOnUnits K F) ⟶ Rep.ofAlgebraAutOnUnits K E := by
    apply Rep.ofHom
    refine ⟨(Units.mapEquiv e.toMulEquiv).toAdditive.toIntLinearEquiv.toLinearMap, ?_⟩
    intro σ
    apply LinearMap.ext
    intro a
    apply Units.ext
    change e (e.symm (σ (e ((show Additive Fˣ from a).toMul : F)))) =
      σ (e ((show Additive Fˣ from a).toMul : F))
    exact e.apply_symm_apply _
  change groupCohomology.map (AlgEquiv.autCongr e).symm.toMonoidHom φ 2 ≫
      groupCohomology.map (AlgEquiv.restrictNormalHom E)
        (finiteGaloisUnitsInflationRepHom K N E) 2 =
    finiteGaloisTowerUnitsH2Inflation K F N
  refine (groupCohomology.map_comp
    (A := Rep.ofAlgebraAutOnUnits K F) (B := Rep.ofAlgebraAutOnUnits K E)
    (C := Rep.ofAlgebraAutOnUnits K N) (AlgEquiv.autCongr e).symm.toMonoidHom
    (AlgEquiv.restrictNormalHom E) φ (finiteGaloisUnitsInflationRepHom K N E) 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ x
    apply (algebraMap F N).injective
    change algebraMap F N (e.symm (σ.restrictNormal E (e x))) =
      algebraMap F N (σ.restrictNormal F x)
    have heval (y : E) : algebraMap F N (e.symm y) = (y : N) :=
      congrArg (fun z : E ↦ (z : N)) (e.apply_symm_apply y)
    rw [heval]
    exact (σ.restrictNormal_commutes E (e x)).trans
      (σ.restrictNormal_commutes F x).symm
  · apply LinearMap.ext
    intro a
    apply Units.ext
    rfl

/-- Field-unit inflation is injective for an arbitrary finite Galois tower. -/
theorem finiteGaloisTowerUnitsH2Inflation_injective
    [Normal K F] [FiniteDimensional K N] [IsGalois K N] :
    Function.Injective (finiteGaloisTowerUnitsH2Inflation K F N).hom := by
  let i : F →ₐ[K] N := IsScalarTower.toAlgHom K F N
  have : Normal K i.fieldRange := Normal.of_algEquiv i.equivFieldRange
  let c := unitsCohomologyCongrTop K F i.fieldRange i.equivFieldRange 2
  intro x y hxy
  apply c.toLinearEquiv.injective
  apply finiteGaloisUnitsH2Inflation_injective K N i.fieldRange
  have hx := congrArg (fun f ↦ f.hom x) (fieldRange_inflation K F N)
  have hy := congrArg (fun f ↦ f.hom y) (fieldRange_inflation K F N)
  exact hx.trans (hxy.trans hy.symm)

private theorem restriction_surjectiveScalars
    (E : Type) [Field E] [Algebra K E] [Algebra E N] [IsScalarTower K E N]
    [Algebra F E] [IsScalarTower F E N]
    (h : Function.Surjective (algebraMap F E)) :
    finiteGaloisTowerUnitsH2Restriction K E N ≫
      (unitsCohomologyRestrictScalarsIso F E N h 2).hom =
        finiteGaloisTowerUnitsH2Restriction K F N := by
  let t : Gal(N/F) ≃* Gal(N/E) := AlgEquiv.extendScalarsHomOfSurjective h
  let ψ : Rep.res t.toMonoidHom (Rep.ofAlgebraAutOnUnits E N) ⟶
      Rep.ofAlgebraAutOnUnits F N := Rep.ofHom ⟨LinearMap.id, fun _ ↦ rfl⟩
  change groupCohomology.map (AlgEquiv.restrictScalarsHom K)
      (finiteGaloisTowerUnitsRestrictionRepHom K E N) 2 ≫
    groupCohomology.map t.toMonoidHom ψ 2 =
      finiteGaloisTowerUnitsH2Restriction K F N
  refine (groupCohomology.map_comp
    (A := Rep.ofAlgebraAutOnUnits K N) (B := Rep.ofAlgebraAutOnUnits E N)
    (C := Rep.ofAlgebraAutOnUnits F N) (AlgEquiv.restrictScalarsHom K)
    t.toMonoidHom (finiteGaloisTowerUnitsRestrictionRepHom K E N) ψ 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · apply LinearMap.ext
    intro a
    rfl

/-- Middle exactness for unit H² in an arbitrary finite Galois tower. -/
theorem finiteGaloisTowerUnitsH2Restriction_ker_le_inflation_range
    [Normal K F] [FiniteDimensional K N] [IsGalois K N] :
    (finiteGaloisTowerUnitsH2Restriction K F N).hom.ker ≤
      (finiteGaloisTowerUnitsH2Inflation K F N).hom.range := by
  let i : F →ₐ[K] N := IsScalarTower.toAlgHom K F N
  let E : IntermediateField K N := i.fieldRange
  let e : F ≃ₐ[K] E := i.equivFieldRange
  have : Normal K E := Normal.of_algEquiv e
  let : Algebra F E := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower F E N := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  have hsur : Function.Surjective (algebraMap F E) := e.surjective
  let c := unitsCohomologyRestrictScalarsIso F E N hsur 2
  intro x hx
  have hxE : (finiteGaloisUnitsH2Restriction K N E).hom x = 0 := by
    rw [restriction_intermediateField K N E]
    apply c.toLinearEquiv.injective
    rw [map_zero]
    exact (congrArg (fun f : groupCohomology (Rep.ofAlgebraAutOnUnits K N) 2 ⟶
        groupCohomology (Rep.ofAlgebraAutOnUnits F N) 2 ↦ f.hom x)
      (restriction_surjectiveScalars K F N E hsur)).trans hx
  obtain ⟨y, hy⟩ := finiteGaloisUnitsH2Restriction_ker_le_inflation_range K N E hxE
  let d := unitsCohomologyCongrTop K F E e 2
  refine ⟨d.inv y, ?_⟩
  have hinf := congrArg (fun f ↦ f.hom (d.inv y)) (fieldRange_inflation K F N)
  have hcancel : d.hom (d.inv y) = y := d.toLinearEquiv.apply_symm_apply y
  exact hinf.symm.trans
    ((congrArg (fun z ↦ (finiteGaloisUnitsH2Inflation K N E).hom z) hcancel).trans hy)

end
end ClassFieldTower.Cohomology
