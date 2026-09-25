/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2RadicalFunctional
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportInertiaCorrection
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.AbsoluteInertiaUnramifiedFactor
import GaloisCohomology.ProP.H2CocycleExtensionLinearLiftDifference

set_option autoImplicit false
/-!
# The actual radical functional detects stage inflation

A zero radical functional supplies a global character agreeing with the
chosen lift's inertia defects. Correcting the lift by this character kills
every finite inertia group. The actual maximal-unramified factor therefore
lifts the stage quotient, forcing its inflated degree-two class to vanish.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.Cohomology ClassFieldTower.ProP ClassFieldTower.Martinet ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))

local notation "StageQuotient" => MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ) ⧸
  (U : Subgroup (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))
local notation "StageH2" => continuousCohomologyZModPLifted (n : ℕ) StageQuotient 2

local instance arithmeticRadicalKernelTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance arithmeticRadicalKernelDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _

/-- Vanishing of the actual ideal-radical functional forces the stage
class to vanish in the maximal everywhere-unramified pro-p group. -/
theorem arithmeticStageH2RadicalFunctional_eq_zero_imp_inflation_eq_zero
    (x : StageH2) (hx : arithmeticStageH2RadicalFunctional F n hpOdd U x = 0) :
    (continuousCohomologyZModPMapLifted (n : ℕ)
      (quotientProjection (U : Subgroup
        (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))) 2).hom x = 0 := by
  classical
  let S := arithmeticStageH2UniformRamifiedPlaces F n hpOdd U
  obtain ⟨gamma, hinside, houtside⟩ :=
    exists_absoluteCharacter_of_finiteSupport_radical_annihilator F n S
      (fun v => arithmeticStageH2GlobalLocalDifferenceCharacter F n hpOdd U x v.1) hx
  let z := degreeTwoCocycleRepresentative x
  let s := H2CocycleExtension.twistByCharacter z
    (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U x) gamma
  have hs : ∀ v : HeightOneSpectrum (𝓞 F),
      ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
        s (finitePlaceAbsoluteDecompositionInclusion F v
          (finitePlaceAbsoluteInertiaInclusion F v sigma)) = 1 := by
    intro v sigma
    by_cases hv : v ∈ S
    · have hkill := (H2CocycleExtension.twistByCharacter_kills_subgroup_iff z
        (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v)
        (arithmeticStageH2AbsoluteLocalLift F (n : ℕ) U x v)
        ((arithmeticStageH2GlobalLiftAtFinitePlace_projection F n hpOdd U x v).trans
          (arithmeticStageH2AbsoluteLocalLift_projection F (n : ℕ) U x v).symm)
        (gamma.comp (finitePlaceAbsoluteDecompositionInclusion F v))
        (finitePlaceAbsoluteInertiaSubgroup F v)
        (arithmeticStageH2AbsoluteLocalLift_inertia_le_ker F (n : ℕ) U x v)).2
        (by
          ext tau
          exact hinside ⟨v, hv⟩ tau)
      exact hkill sigma.property
    · have hg : arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v sigma.1 = 1 :=
        arithmeticStageH2GlobalLiftAtFinitePlace_inertia_le_ker_of_not_mem_uniform
          F n hpOdd U x v hv sigma.property
      have hgamma := houtside v hv sigma
      apply H2CocycleExtension.ext
      · change (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v sigma.1).left -
          ULift.up (gamma (finitePlaceAbsoluteDecompositionInclusion F v sigma.1)).toAdd = 0
        rw [hg, hgamma]
        exact sub_self _
      · change (arithmeticStageH2GlobalLiftAtFinitePlace F n hpOdd U x v sigma.1).right = 1
        rw [hg]
        rfl
  have hQ : IsPGroup (n : ℕ) StageQuotient :=
    ((maxEverywhereUnramifiedProPGaloisGroup_hasPGroupOpenNormalBasis F (n : ℕ) hpOdd).quotient_mem
      (FiniteGroupClass.pGroup_formation (n : ℕ)) U).2
  obtain ⟨t, ht⟩ := exists_maxEverywhereUnramifiedProP_factor_of_inertia_trivial
    F (n : ℕ) hpOdd (H2CocycleExtension.isPGroup z hQ) s hs
  have hproj : (H2CocycleExtension.projection z).comp s =
      arithmeticStageAbsoluteQuotientMap F n U :=
    (H2CocycleExtension.twistByCharacter_projection z
      (arithmeticStageH2AbsoluteGlobalLift F n hpOdd U x) gamma).trans
      (arithmeticStageH2AbsoluteGlobalLift_projection F n hpOdd U x)
  have htproj : (H2CocycleExtension.projection z).comp t =
      quotientProjection (U : Subgroup
        (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ))) := by
    ext tau
    obtain ⟨sigma, rfl⟩ := absoluteToMaxEverywhereUnramifiedProP_surjective F (n : ℕ) tau
    exact (congrArg (H2CocycleExtension.projection z) (DFunLike.congr_fun ht sigma)).trans
      (DFunLike.congr_fun hproj sigma)
  rw [← degreeTwoCocycleRepresentative_π x]
  exact H2CocycleExtension.restriction_eq_zero_of_lift
    (quotientProjection (U : Subgroup
      (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ)))) z t htproj

end ClassFieldTower.Martinet.Shafarevich
