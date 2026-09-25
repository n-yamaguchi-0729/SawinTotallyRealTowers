/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteTransgressionKernel
import ProCGroups.Cohomology.InvariantCharacterFiniteStage
import GaloisCohomology.ProP.QuotientRestriction

set_option autoImplicit false
/-!
# Inflation of finite-stage transgression classes

For a closed normal subgroup `R` and an ambient finite quotient `F/U`, this file constructs the
canonical map from `F/R` to `(F/U)/(image R)` and uses it to inflate the finite factor-set class.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

local instance finiteStageTargetTopology
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    TopologicalSpace
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) := ⊥

local instance finiteStageTargetDiscrete
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    DiscreteTopology
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) :=
  discreteTopology_bot _

variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- The finite-stage quotient map from `F/R` to the quotient by the image of `R`. -/
def finiteStageQuotientMap
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    F ⧸ (R : Subgroup F) →ₜ*
      (F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U where
  toMonoidHom := QuotientGroup.lift (R : Subgroup F)
    ((QuotientGroup.mk' (finiteStageImage R U)).comp
      (QuotientGroup.mk' (U.1 : Subgroup F))) (by
        intro r hr
        apply (QuotientGroup.eq_one_iff
          (N := finiteStageImage R U)
          (QuotientGroup.mk' (U.1 : Subgroup F) r)).2
        exact ⟨r, hr, rfl⟩)
  continuous_toFun := by
    apply Continuous.quotient_lift
    exact (continuous_of_discreteTopology : Continuous
      (fun q : F ⧸ (U.1 : Subgroup F) ↦
        QuotientGroup.mk' (finiteStageImage R U) q)).comp
          (OpenNormalSubgroup.quotientProj U.1).continuous

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem finiteStageQuotientMap_mk
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (f : F) :
    finiteStageQuotientMap R U (QuotientGroup.mk' (R : Subgroup F) f) =
      QuotientGroup.mk' (finiteStageImage R U)
        (QuotientGroup.mk' (U.1 : Subgroup F) f) :=
  rfl

/-- Inflate a finite factor-set transgression class to the original quotient `F/R`. -/
noncomputable def inflatedFiniteTransgressionClass
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χbar : MonoidHom (finiteStageImage R U) (Multiplicative (ZMod p)))
    (hχbar : ∀ (g : F ⧸ (U.1 : Subgroup F)) (n : finiteStageImage R U),
      χbar (MulAut.conjNormal g n) = χbar n) :
    ClassFieldTower.Cohomology.continuousCohomologyZModPLifted p
      (F ⧸ (R : Subgroup F)) 2 :=
  ClassFieldTower.Cohomology.continuousCohomologyZModPMapLifted p
      (finiteStageQuotientMap R U) 2
    (ClassFieldTower.Cohomology.finiteTransgressionClass
      (finiteStageImage R U) χbar hχbar)

end

end ClassFieldTower.ProP
