/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.ArithmeticStageChosenUnramified
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.EverywhereUnramifiedSupportedIdeleH2

set_option autoImplicit false
/-!
# Integral idele primitives at the actual arithmetic stage

The open-normal arithmetic stage supplies both finite- and infinite-place
unramifiedness. Thus its everywhere-integral relative idele subgroup has
zero H², and every supported two-cocycle has an actual idele primitive.
There are no new local vanishing, Shapiro, or glue hypotheses.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet ClassFieldTower.Cohomology ProCGroups

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime] (hpOdd : Odd p)
variable (U : OpenNormalSubgroup (MaxEverywhereUnramifiedProPGaloisGroup F p))

local notation "StageField" => FiniteEverywhereUnramifiedProPExtension.field
  (openNormalArithmeticStage F p hpOdd U)
local notation "J" => relativeIdeleLocalTensorDecompositionSupportedSubgroup
  (K := F) (L := StageField) ∅

local instance arithmeticStageSupportedH2IdeleAction : MulDistribMulAction Gal(StageField / F) J :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := F) (L := StageField) ∅

/-- The actual arithmetic stage has zero H² on everywhere-integral
relative ideles. -/
theorem openNormalArithmeticStage_supportedIdeleH2_subsingleton :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(StageField / F) J) 2) :=
  everywhereUnramifiedSupportedIdeleH2_subsingleton F StageField
    (openNormalArithmeticStage_chosenFinitePlaceIsUnramified F p hpOdd U)
    (fun v ↦ (openNormalArithmeticStage F p hpOdd U).everywhereUnramified.infinitePlaces.1
      (chosenInfinitePlaceAbove (L := StageField) v))

/-- Every two-cocycle in the arithmetic stage's everywhere-integral
relative ideles admits an actual one-cochain primitive in that subgroup. -/
theorem openNormalArithmeticStage_supportedIdeleTwoCocycle_isCoboundary
    (f : Gal(StageField / F) × Gal(StageField / F) → J)
    (hf : groupCohomology.IsMulCocycle₂ f) : groupCohomology.IsMulCoboundary₂ f := by
  let _ := openNormalArithmeticStage_supportedIdeleH2_subsingleton F p hpOdd U
  exact isMulCoboundary₂_of_H2_subsingleton f hf

end ClassFieldTower.Martinet.Shafarevich
