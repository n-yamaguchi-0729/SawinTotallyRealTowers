/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.FiniteStageTransgressionExact
import Nyll.GaloisCohomology.ProP.FiniteTransgressionQuotient

/-!
# Quotient presentation of finite-stage transgression

At a finite quotient stage, invariant characters modulo restrictions of continuous degree-one
characters identify with the range of finite transgression.
-/

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC
open ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F]

local instance finiteStageQuotientZModTopology : TopologicalSpace (ZMod p) := ⊥
local instance finiteStageQuotientZModDiscrete : DiscreteTopology (ZMod p) :=
  discreteTopology_bot _

local instance finiteStageQuotientContinuousH1Module
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    Module (ZMod p)
      (ContinuousH1ZMod (p := p) (G := F ⧸ (U.1 : Subgroup F))) :=
  continuousH1ZModModule

/-- Invariant finite-stage characters modulo continuous ambient restrictions are linearly
equivalent to the finite-transgression range. -/
noncomputable def finiteStageContinuousCharacterQuotientEquivTransgressionRange
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    (InvariantFiniteCharacter (p := p) (finiteStageImage R U) ⧸
        LinearMap.range (finiteStageContinuousCharacterRestrictionLinearMap R U)) ≃ₗ[ZMod p]
      LinearMap.range
        (finiteTransgressionLinearMap (p := p) (finiteStageImage R U)) :=
  (Submodule.quotEquivOfEq _ _
      ((finiteStageContinuousCharacterRestriction_range_eq_transgression_ker R U).trans
        (finiteCharacterRestriction_range_eq_transgression_ker
          (p := p) (finiteStageImage R U)).symm)).trans
    (finiteTransgressionQuotientEquivRange (p := p) (finiteStageImage R U))

@[simp]
theorem finiteStageContinuousCharacterQuotientEquivTransgressionRange_apply_mk
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χ : InvariantFiniteCharacter (p := p) (finiteStageImage R U)) :
    finiteStageContinuousCharacterQuotientEquivTransgressionRange R U
        (Submodule.Quotient.mk χ) =
      ⟨finiteTransgressionLinearMap (finiteStageImage R U) χ,
        LinearMap.mem_range_self
          (finiteTransgressionLinearMap (finiteStageImage R U)) χ⟩ := by
  rfl

/-- The continuous-character quotient and the finite-stage transgression range have equal
`ZMod p`-dimension. -/
theorem finrank_finiteStageContinuousCharacterQuotient_eq_transgressionRange
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    Module.finrank (ZMod p)
        (InvariantFiniteCharacter (p := p) (finiteStageImage R U) ⧸
          LinearMap.range (finiteStageContinuousCharacterRestrictionLinearMap R U)) =
      Module.finrank (ZMod p)
        (LinearMap.range
          (finiteTransgressionLinearMap (p := p) (finiteStageImage R U))) :=
  (finiteStageContinuousCharacterQuotientEquivTransgressionRange R U).finrank_eq

end

end ClassFieldTower.ProP
