/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
import GaloisCohomology.Kummer.FiniteGaloisBaseUnitsH2Naturality
import GaloisCohomology.Kummer.FiniteGaloisUnitsCohomologyTransport
import GaloisCohomology.Kummer.FiniteGaloisUnitsH2Inflation
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedBaseUnitsH2
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped ValuativeRel

namespace LocalClassFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField ClassFieldTower.Cohomology

/-- A cyclic lower-field H² class becomes zero after inflation to an
unramified relative extension whose degree divides the lower ramification index. -/
theorem finiteCyclicUnitsH2_inflation_restriction_eq_zero
    (K N : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field N] [Algebra K N] [ValuativeRel N] [TopologicalSpace N]
    [IsNonarchimedeanLocalField N]
    (L M : IntermediateField K N)
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional L N] [IsGalois L N]
    [FiniteDimensional K M] [IsGalois K M] [IsCyclic Gal(M/K)]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Valuation.HasExtension (ValuativeRel.valuation L) (ValuativeRel.valuation N)]
    [Module.Finite 𝒪[L] 𝒪[N]] [IsUnramifiedValuedExtension L N]
    (hd : Module.finrank L N ∣ (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K]) :
    finiteGaloisUnitsH2Inflation K N M ≫ finiteGaloisUnitsH2Restriction K N L = 0 := by
  have h := finiteGaloisBaseUnitsH2_inflation_restriction K N L M
  rw [finiteTowerBaseUnitsH2Map_eq_zero_of_finrank_dvd_ramificationIdx K L N hd,
    comp_zero] at h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := finiteCyclicBaseUnitsH2Map_surjective K M x
  have hvalue := congrArg (fun f :
      groupCohomology (Rep.trivial ℤ Gal(M/K) (Additive Kˣ)) 2 ⟶
        groupCohomology (Rep.ofAlgebraAutOnUnits L N) 2 => f.hom a) h
  change (finiteGaloisUnitsH2Restriction K N L).hom
      ((finiteGaloisUnitsH2Inflation K N M).hom
        ((finiteGaloisBaseUnitsH2Map K M).hom a)) = 0 at hvalue
  change (finiteGaloisUnitsH2Restriction K N L).hom
      ((finiteGaloisUnitsH2Inflation K N M).hom x) = 0
  rw [ha] at hvalue
  exact hvalue

end LocalClassFieldTheory
