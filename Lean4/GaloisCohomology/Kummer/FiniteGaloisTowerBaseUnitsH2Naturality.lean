/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
import GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2
import GaloisCohomology.Kummer.FiniteTowerBaseUnitsH2
import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

set_option autoImplicit false

open CategoryTheory
namespace ClassFieldTower.Cohomology
noncomputable section
variable (K N L M : Type) [Field K] [Field N] [Field L] [Field M]
variable [Algebra K N] [Algebra K L] [Algebra L N] [IsScalarTower K L N]
variable [Algebra K M] [Algebra M N] [IsScalarTower K M N] [Normal K M]

/-- Inflate a base-unit class from the normal intermediate field and restrict
it to the relative Galois group. The result is its actual group restriction
with the coefficient map along K → L → N. -/
theorem finiteGaloisTowerBaseUnitsH2_inflation_restriction :
    finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisTowerUnitsH2Inflation K M N ≫
      finiteGaloisTowerUnitsH2Restriction K L N =
    groupCohomology.map
      (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (B := Rep.trivial ℤ Gal(N/L) (Additive Kˣ))
      ((AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M).comp
        (AlgEquiv.restrictScalarsHom K))
      (𝟙 (Rep.trivial ℤ Gal(N/L) (Additive Kˣ))) 2 ≫
      finiteTowerBaseUnitsH2Map K L N := by
  let r : Gal(N/K) →* Gal(M/K) := AlgEquiv.restrictNormalHom (F := K) (K₁ := N) M
  let t : Gal(N/L) →* Gal(N/K) := AlgEquiv.restrictScalarsHom K
  let φ : Rep.res r (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) ⟶
      Rep.ofAlgebraAutOnUnits K N :=
    (Rep.resFunctor r).map (finiteGaloisBaseUnitsRepHom K M) ≫
      finiteGaloisTowerUnitsInflationRepHom K M N
  have hFirst : finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisTowerUnitsH2Inflation K M N =
      groupCohomology.map r φ 2 :=
    (groupCohomology.map_comp
      (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (B := Rep.ofAlgebraAutOnUnits K M) (C := Rep.ofAlgebraAutOnUnits K N)
      (MonoidHom.id Gal(M/K)) r
      (finiteGaloisBaseUnitsRepHom K M) (finiteGaloisTowerUnitsInflationRepHom K M N) 2).symm
  let ψ : Rep.res (r.comp t) (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) ⟶
      Rep.ofAlgebraAutOnUnits L N :=
    (Rep.resFunctor t).map φ ≫ finiteGaloisTowerUnitsRestrictionRepHom K L N
  have hSecond : groupCohomology.map r φ 2 ≫
      groupCohomology.map t (finiteGaloisTowerUnitsRestrictionRepHom K L N) 2 =
      groupCohomology.map (r.comp t) ψ 2 :=
    (groupCohomology.map_comp
      (A := Rep.trivial ℤ Gal(M/K) (Additive Kˣ))
      (B := Rep.ofAlgebraAutOnUnits K N) (C := Rep.ofAlgebraAutOnUnits L N)
      r t φ (finiteGaloisTowerUnitsRestrictionRepHom K L N) 2).symm
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
    finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisTowerUnitsH2Inflation K M N ≫
        finiteGaloisTowerUnitsH2Restriction K L N =
      (finiteGaloisBaseUnitsH2Map K M ≫ finiteGaloisTowerUnitsH2Inflation K M N) ≫
        groupCohomology.map t (finiteGaloisTowerUnitsRestrictionRepHom K L N) 2 := by
          rw [finiteGaloisTowerUnitsH2Restriction, Category.assoc]
    _ = groupCohomology.map r φ 2 ≫
        groupCohomology.map t (finiteGaloisTowerUnitsRestrictionRepHom K L N) 2 :=
      congrArg (fun (f : groupCohomology (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) 2 ⟶
        groupCohomology (Rep.ofAlgebraAutOnUnits K N) 2) =>
          f ≫ groupCohomology.map t (finiteGaloisTowerUnitsRestrictionRepHom K L N) 2) hFirst
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
