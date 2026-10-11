/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.RelationIdealPrimitive

/-!
# Fox differential: completed — finite stage — source cycle reduction

The principal declarations in this module are:

- `foxAlgebraicStageSourceBoundaryCycleSubmodule`
  Source boundary cycles in the source coordinate module.
- `foxAlgebraicStageSourceCycleProjectionExact`
  Source-cycle projection exactness: every source Fox cycle maps to the target relation-boundary
  submodule. This is the source-quotient analogue of exactness before the relation-ideal correction.
- `mem_foxAlgebraicStageSourceBoundaryCycleSubmodule`
  Membership in the finite-stage boundary-cycle object is characterized by the corresponding
  boundary-vanishing condition.
- `foxAlgebraicStageSourceBoundaryLeftRelationReduction_of_sourceCycleProjectionExact`
  Source-cycle projection exactness implies the reduction for the left relation-augmentation
  submodule, because elements of the left relation-augmentation submodule have explicit
  relation-compatible primitives.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Source boundary cycles in the source coordinate module. -/
def foxAlgebraicStageSourceBoundaryCycleSubmodule [Fintype X] :
    Submodule (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
      (foxAlgebraicStageSourceCoordinateVector (X := X) N n) :=
  LinearMap.ker (foxAlgebraicStageSourceFoxBoundary (X := X) N n)

omit [DecidableEq X] [N.Normal] in
/--
Membership in the finite-stage boundary-cycle object is characterized by the corresponding
boundary-vanishing condition.
-/
@[simp]
theorem mem_foxAlgebraicStageSourceBoundaryCycleSubmodule
    (N : Subgroup (FreeGroup X)) (n : ℕ) [Fintype X]
    {p : foxAlgebraicStageSourceCoordinateVector (X := X) N n} :
    p ∈ foxAlgebraicStageSourceBoundaryCycleSubmodule (X := X) N n ↔
      foxAlgebraicStageSourceFoxBoundary (X := X) N n p = 0 :=
  Iff.rfl

/--
Source-cycle projection exactness: every source Fox cycle maps to the target relation-boundary
submodule. This is the source-quotient analogue of exactness before the relation-ideal
correction.
-/
def foxAlgebraicStageSourceCycleProjectionExact [Fintype X] : Prop :=
  ∀ p : foxAlgebraicStageSourceCoordinateVector (X := X) N n,
    p ∈ foxAlgebraicStageSourceBoundaryCycleSubmodule (X := X) N n →
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n p ∈
        foxAlgebraicStageRelationBoundarySubmodule (X := X) N n

/-- Left-submodule version of the source-boundary reduction. -/
def foxAlgebraicStageSourceBoundaryLeftRelationReduction [Fintype X] : Prop :=
  ∀ a : foxAlgebraicStageSourceCoordinateVector (X := X) N n,
    foxAlgebraicStageSourceFoxBoundary (X := X) N n a ∈
      foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n →
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a ∈
        foxAlgebraicStageRelationBoundarySubmodule (X := X) N n

/--
Source-cycle projection exactness implies the reduction for the left relation-augmentation
submodule, because elements of the left relation-augmentation submodule have explicit
relation-compatible primitives.
-/
theorem foxAlgebraicStageSourceBoundaryLeftRelationReduction_of_sourceCycleProjectionExact
    [Fintype X]
    (hcycle : foxAlgebraicStageSourceCycleProjectionExact (X := X) N n) :
    foxAlgebraicStageSourceBoundaryLeftRelationReduction (X := X) N n := by
  intro a ha
  rcases foxAlgebraicStageSourceBoundaryPrimitive_of_mem_relationAugmentationLeftSubmodule
      (X := X) N n ha with ⟨p, hpboundary, hprel⟩
  have hcycle_ap :
      a - p ∈ foxAlgebraicStageSourceBoundaryCycleSubmodule (X := X) N n := by
    change foxAlgebraicStageSourceFoxBoundary (X := X) N n (a - p) = 0
    rw [map_sub, hpboundary]
    exact sub_self _
  have haprel := hcycle (a - p) hcycle_ap
  have hmap :
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a =
        foxAlgebraicStageCoordinateSourceToTarget (X := X) N n p +
          foxAlgebraicStageCoordinateSourceToTarget (X := X) N n (a - p) := by
    have hsub := map_sub (foxAlgebraicStageCoordinateSourceToTarget (X := X) N n) a p
    calc
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a =
          foxAlgebraicStageCoordinateSourceToTarget (X := X) N n p +
            (foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a -
              foxAlgebraicStageCoordinateSourceToTarget (X := X) N n p) := by
            abel
      _ = foxAlgebraicStageCoordinateSourceToTarget (X := X) N n p +
            foxAlgebraicStageCoordinateSourceToTarget (X := X) N n (a - p) := by
            rw [← hsub]
  rw [hmap]
  exact (foxAlgebraicStageRelationBoundarySubmodule (X := X) N n).add_mem hprel haprel

/--
If the two-sided relation augmentation ideal is already generated by the same relation
augmentation elements as a left source-submodule, source-cycle projection exactness implies the
source-boundary relation-ideal reduction used in the finite-stage exactness file.
-/
theorem foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_le_leftSubmodule
    [Fintype X]
    (hideal_left :
      ∀ x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n,
        x ∈ foxAlgebraicStageRelationAugmentationIdeal (X := X) N n →
          x ∈ foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n)
    (hcycle : foxAlgebraicStageSourceCycleProjectionExact (X := X) N n) :
    foxAlgebraicStageSourceBoundaryRelationIdealReduction (X := X) N n := by
  intro a ha
  exact foxAlgebraicStageSourceBoundaryLeftRelationReduction_of_sourceCycleProjectionExact
    (X := X) N n hcycle a (hideal_left _ ha)

/-- Finite-stage source-cycle projection exactness gives relation-boundary module exactness. -/
theorem foxAlgebraicStageRelationBoundaryModuleExact_of_relIdealLeftGen_and_sourceCycleProjExact
    [Fintype X]
    (hideal_left :
      ∀ x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n,
        x ∈ foxAlgebraicStageRelationAugmentationIdeal (X := X) N n →
          x ∈ foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n)
    (hcycle : foxAlgebraicStageSourceCycleProjectionExact (X := X) N n) :
    foxAlgebraicStageRelationBoundaryModuleExact (X := X) N n :=
  foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
    (X := X) N n
    (foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_le_leftSubmodule
      (X := X) N n hideal_left hcycle)

/-- The same inputs give finite coordinate coverage. -/
theorem foxAlgebraicStageBoundaryCyclesCovered_of_relIdealLeftGen_and_sourceCycleProjExact
    [Fintype X]
    (hideal_left :
      ∀ x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n,
        x ∈ foxAlgebraicStageRelationAugmentationIdeal (X := X) N n →
          x ∈ foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n)
    (hcycle : foxAlgebraicStageSourceCycleProjectionExact (X := X) N n) :
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryModuleExact
    (X := X) N n
    (foxAlgebraicStageRelationBoundaryModuleExact_of_relIdealLeftGen_and_sourceCycleProjExact
      (X := X) N n hideal_left hcycle)

/--
Relation-ideal left generation together with exactness of the source-cycle projection covers the
finite semidirect boundary cycles.
-/
theorem foxAlgebraicStageSemiBoundaryCyclesCovered_of_relIdealLeftGen_and_sourceCycleProjExact
    [Fintype X]
    (hideal_left :
      ∀ x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n,
        x ∈ foxAlgebraicStageRelationAugmentationIdeal (X := X) N n →
          x ∈ foxAlgebraicStageRelationAugmentationLeftSubmodule (X := X) N n)
    (hcycle : foxAlgebraicStageSourceCycleProjectionExact (X := X) N n) :
    foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  foxAlgebraicStageSemiBoundaryCyclesCovered_of_sourceBoundaryRelReduction
    (X := X) N n
    (foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_le_leftSubmodule
      (X := X) N n hideal_left hcycle)

end

end FoxDifferential
