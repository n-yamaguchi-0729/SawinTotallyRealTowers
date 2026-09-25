/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2RadicalKernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageH2RadicalLinearMap
import GaloisCohomology.ProP.H2InflationRangeBound
import Mathlib.LinearAlgebra.Dimension.LinearMap

set_option autoImplicit false
/-!
# Embedding actual finite-stage inflation ranges in the radical dual

The radical functional detects zero after inflation. A linear section of
the map onto the inflation range therefore gives an injective map from
that range to the radical dual. This uses only the proved kernel inclusion;
no compatibility of sections at different finite stages is required.
-/

open scoped NumberField Topology
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFieldTower.Martinet ProCGroups ProCGroups.ProC

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))

include hpOdd

/-- Every actual finite-stage inflation range embeds in the fixed arithmetic dual. -/
theorem arithmeticStageH2InflationRange_exists_radicalDual_embedding
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup (n : ℕ))
      (MaxEverywhereUnramifiedProPGaloisGroup F (n : ℕ))) :
    ∃ f : degreeTwoInflationRange (p := (n : ℕ)) U →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (idealPowerRadicalModP F (n : ℕ)), Function.Injective f := by
  let g := (continuousCohomologyZModPMapLifted (n : ℕ)
    (OpenNormalSubgroupInClass.quotientProj U) 2).hom.toLinearMap
  let f := arithmeticStageH2RadicalLinearMap F n hpOdd U.1
  have hker : LinearMap.ker f ≤ LinearMap.ker g := by
    intro x hx
    exact arithmeticStageH2RadicalFunctional_eq_zero_imp_inflation_eq_zero
      F n hpOdd U.1 x (LinearMap.mem_ker.mp hx)
  obtain ⟨s, hs⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  refine ⟨f.comp s, ?_⟩
  intro x y hxy
  change f (s x) = f (s y) at hxy
  have hf : s x - s y ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
  have hg : g (s x - s y) = 0 := hker hf
  have hx : g (s x) = x.val := congrArg Subtype.val (LinearMap.congr_fun hs x)
  have hy : g (s y) = y.val := congrArg Subtype.val (LinearMap.congr_fun hs y)
  apply Subtype.ext
  simpa only [map_sub, hx, hy, sub_eq_zero] using hg

end ClassFieldTower.Martinet.Shafarevich
