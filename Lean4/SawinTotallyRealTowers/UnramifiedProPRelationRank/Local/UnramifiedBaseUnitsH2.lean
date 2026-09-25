/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteTowerBaseUnitsH2
import GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedBaseUnitNorm
import ValuedFieldTheory.LocalField.NormUnits
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

set_option autoImplicit false

/-!
# Vanishing of base-unit H² in an unramified local tower

In K → L → N with N/L unramified and [N:L] dividing e(L/K), every
K-unit embedded in L has an actual norm preimage from N. The cyclic
coefficient criterion therefore kills the whole degree-two map.
-/

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open ClassFieldTower.Cohomology

/-- The coefficient map from base-field units vanishes when the unramified
top degree divides the ramification index of the lower extension. -/
theorem finiteTowerBaseUnitsH2Map_eq_zero_of_finrank_dvd_ramificationIdx
    (K L N : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Field N] [ValuativeRel N] [TopologicalSpace N]
    [IsNonarchimedeanLocalField N]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra L N] [FiniteDimensional L N] [IsGalois L N]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Valuation.HasExtension (ValuativeRel.valuation L)
      (ValuativeRel.valuation N)]
    [Module.Finite 𝒪[L] 𝒪[N]] [IsUnramifiedValuedExtension L N]
    (hd : Module.finrank L N ∣
      (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K]) :
    finiteTowerBaseUnitsH2Map K L N = 0 := by
  have : IsIntegralClosure 𝒪[N] 𝒪[L] N :=
    localCompleteDVF_integerRing_isIntegralClosure L N
  have : IsCyclic Gal(N/L) := isCyclic_galoisGroup_of_unramifiedValuation L N
  let : CommGroup Gal(N/L) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(N/L))
  apply finiteCyclicH2_coefficientMap_eq_zero_of_norm
    (Rep.trivial ℤ Gal(N/L) (Additive Kˣ)) (Rep.ofAlgebraAutOnUnits L N)
    g hg (finiteTowerBaseUnitsRepHom K L N)
  intro a
  let x : Kˣ := (show Additive Kˣ from a.val).toMul
  obtain ⟨y, hy⟩ :=
    exists_normUnits_eq_mapBaseUnitsToExtensionUnits_of_finrank_dvd_ramificationIdx
      K L N hd x
  refine ⟨Additive.ofMul y, ?_⟩
  apply Units.ext
  exact (groupCohomology.norm_ofAlgebraAutOnUnits_eq (K := L) y).trans
    (congrArg (fun u : Lˣ ↦ algebraMap L N (u : L)) hy)

end LocalClassFieldTheory
