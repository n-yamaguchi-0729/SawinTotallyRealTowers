/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
import GaloisCohomology.Kummer.FiniteGaloisUnitsH2Inflation
import GaloisCohomology.Kummer.FiniteGaloisUnitsCohomologyTransport
import GaloisCohomology.Kummer.FiniteTowerBaseUnitsH2
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false

/-!
# Base-unit inflation and restriction

The two routes through a finite Galois tower are compared using their actual
group restriction and coefficient maps. This comparison is used to turn
relative norm primitives into vanishing of restricted inflated H² classes.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K N : Type) [Field K] [Field N] [Algebra K N]
variable (L M : IntermediateField K N)

private def relativeRestrictionHom : Gal(N/L) →* Gal(N/K) :=
  L.fixingSubgroup.subtype.comp L.fixingSubgroupEquiv.symm.toMonoidHom

private def relativeUnitsRepHom :
    Rep.res (relativeRestrictionHom K N L) (Rep.ofAlgebraAutOnUnits K N) ⟶
      Rep.ofAlgebraAutOnUnits L N := by
  apply Rep.ofHom
  exact ⟨LinearMap.id, fun _ => rfl⟩

private def relativeSubgroupUnitsRepHom :
    Rep.res L.fixingSubgroupEquiv.symm.toMonoidHom
      (Rep.res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N)) ⟶
      Rep.ofAlgebraAutOnUnits L N := by
  apply Rep.ofHom
  exact ⟨LinearMap.id, fun _ => rfl⟩

private theorem unitsH2Restriction_eq_map :
    finiteGaloisUnitsH2Restriction K N L =
      groupCohomology.map (relativeRestrictionHom K N L) (relativeUnitsRepHom K N L) 2 := by
  change groupCohomology.map L.fixingSubgroup.subtype
      (𝟙 (Rep.res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N))) 2 ≫
    groupCohomology.map L.fixingSubgroupEquiv.symm.toMonoidHom
      (relativeSubgroupUnitsRepHom K N L) 2 =
    groupCohomology.map (relativeRestrictionHom K N L) (relativeUnitsRepHom K N L) 2
  refine (groupCohomology.map_comp
    (A := Rep.ofAlgebraAutOnUnits K N)
    (B := Rep.res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N))
    (C := Rep.ofAlgebraAutOnUnits L N) L.fixingSubgroup.subtype
    L.fixingSubgroupEquiv.symm.toMonoidHom
    (𝟙 (Rep.res L.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K N)))
    (relativeSubgroupUnitsRepHom K N L) 2).symm.trans ?_
  apply groupCohomology.map_congr
  · rfl
  · apply LinearMap.ext
    intro a
    rfl

variable [Normal K M]

/-- Inflate a base-unit class from the normal intermediate field and restrict
it to the relative Galois group. The result is its actual group restriction
with the coefficient map along K → L → N. -/
theorem finiteGaloisBaseUnitsH2_inflation_restriction :
    finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisUnitsH2Inflation K N M ≫
      finiteGaloisUnitsH2Restriction K N L =
    groupCohomology.map
      (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (B := Rep.trivial ℤ Gal(N/L) (Additive Kˣ))
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp
        (L.fixingSubgroup.subtype.comp L.fixingSubgroupEquiv.symm.toMonoidHom))
      (𝟙 (Rep.trivial ℤ Gal(N/L) (Additive Kˣ))) 2 ≫
      finiteTowerBaseUnitsH2Map K L N := by
  let r : Gal(N/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M
  let t : Gal(N/L) →* Gal(N/K) := relativeRestrictionHom K N L
  let φ : Rep.res r (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) ⟶
      Rep.ofAlgebraAutOnUnits K N :=
    (Rep.resFunctor r).map (finiteGaloisBaseUnitsRepHom K M) ≫
      finiteGaloisUnitsInflationRepHom K N M
  have hFirst : finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisUnitsH2Inflation K N M =
      groupCohomology.map r φ 2 :=
    (groupCohomology.map_comp
      (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (B := Rep.ofAlgebraAutOnUnits K M) (C := Rep.ofAlgebraAutOnUnits K N)
      (MonoidHom.id Gal(M/K)) r
      (finiteGaloisBaseUnitsRepHom K M) (finiteGaloisUnitsInflationRepHom K N M) 2).symm
  let ψ : Rep.res (r.comp t) (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) ⟶
      Rep.ofAlgebraAutOnUnits L N :=
    (Rep.resFunctor t).map φ ≫ relativeUnitsRepHom K N L
  have hSecond : groupCohomology.map r φ 2 ≫
      groupCohomology.map t (relativeUnitsRepHom K N L) 2 =
      groupCohomology.map (r.comp t) ψ 2 :=
    (groupCohomology.map_comp
      (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (B := Rep.ofAlgebraAutOnUnits K N) (C := Rep.ofAlgebraAutOnUnits L N)
      r t φ (relativeUnitsRepHom K N L) 2).symm
  have hCoefficients : groupCohomology.map (r.comp t) ψ 2 =
      groupCohomology.map (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
        (B := Rep.ofAlgebraAutOnUnits L N) (r.comp t) (finiteTowerBaseUnitsRepHom K L N) 2 := by
    apply groupCohomology.map_congr rfl
    apply LinearMap.ext
    intro a
    apply Units.ext
    exact (IsScalarTower.algebraMap_apply K M N ((show Additive Kˣ from a).toMul : K)).symm.trans
      (IsScalarTower.algebraMap_apply K L N ((show Additive Kˣ from a).toMul : K))
  calc
    finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisUnitsH2Inflation K N M ≫
        finiteGaloisUnitsH2Restriction K N L =
      (finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisUnitsH2Inflation K N M) ≫
        groupCohomology.map t (relativeUnitsRepHom K N L) 2 := by
          rw [unitsH2Restriction_eq_map, Category.assoc]
    _ = groupCohomology.map r φ 2 ≫
        groupCohomology.map t (relativeUnitsRepHom K N L) 2 :=
      congrArg (fun (f : groupCohomology (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) 2 ⟶
        groupCohomology (Rep.ofAlgebraAutOnUnits K N) 2) =>
          f ≫ groupCohomology.map t (relativeUnitsRepHom K N L) 2) hFirst
    _ = groupCohomology.map (r.comp t) ψ 2 := hSecond
    _ = groupCohomology.map (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
        (B := Rep.ofAlgebraAutOnUnits L N) (r.comp t) (finiteTowerBaseUnitsRepHom K L N) 2 := hCoefficients
    _ = groupCohomology.map (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
        (B := Rep.trivial ℤ Gal(N/L) (Additive Kˣ)) (r.comp t)
        (𝟙 (Rep.trivial ℤ Gal(N/L) (Additive Kˣ))) 2 ≫ finiteTowerBaseUnitsH2Map K L N :=
      groupCohomology.map_comp
        (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
        (B := Rep.trivial ℤ Gal(N/L) (Additive Kˣ))
        (C := Rep.ofAlgebraAutOnUnits L N) (r.comp t) (MonoidHom.id Gal(N/L))
        (𝟙 (Rep.trivial ℤ Gal(N/L) (Additive Kˣ))) (finiteTowerBaseUnitsRepHom K L N) 2

end
end ClassFieldTower.Cohomology
