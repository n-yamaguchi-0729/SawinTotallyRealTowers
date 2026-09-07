import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationIdeal
import ProCGroups.FoxDifferential.Completed.FiniteStage.BoundaryQuotient
import ProCGroups.FoxDifferential.Completed.FiniteStage.SemidirectCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — source boundary

The principal declarations in this module are:

- `foxAlgebraicStageSourceCoordinateVector`
  Source-valued coordinate vectors over \((\mathbb{Z}/n\mathbb{Z})[F/([N,N]N^n)]\).
- `foxAlgebraicStageSourceFoxBoundary`
  The source Fox boundary/Euler map \(a \mapsto \sum_i a_i([x_i]-1)\) over the source quotient.
- `foxAlgebraicStageSourceFoxBoundary_apply`
  The finite-stage source Fox boundary is evaluated on the canonical generators and then extended
  linearly to the finite-stage coordinate module.
- `foxAlgebraicStageCoordinateSourceToTarget_apply`
  The finite-stage source-to-target coordinate map is evaluated by applying the target quotient map
  to the chosen coordinate.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Source-valued coordinate vectors over \((\mathbb{Z}/n\mathbb{Z})[F/([N,N]N^n)]\). -/
abbrev foxAlgebraicStageSourceCoordinateVector : Type u :=
  X → foxAlgebraicStageSourceGroupAlgebra (X := X) N n

/-- The source Fox boundary/Euler map \(a \mapsto \sum_i a_i([x_i]-1)\) over the source quotient. -/
def foxAlgebraicStageSourceFoxBoundary [Fintype X] :
    foxAlgebraicStageSourceCoordinateVector (X := X) N n →ₗ[
      foxAlgebraicStageSourceGroupAlgebra (X := X) N n]
      foxAlgebraicStageSourceGroupAlgebra (X := X) N n where
  toFun v :=
    ∑ i : X,
      v i *
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of i)) - 1)
  map_add' := by
    intro v w
    simp only [Pi.add_apply, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, add_mul,
        Finset.sum_add_distrib]
  map_smul' := by
    intro r v
    simp only [Pi.smul_apply, smul_eq_mul, QuotientGroup.mk'_apply, MonoidAlgebra.of_apply,
        mul_assoc,
  RingHom.id_apply, Finset.mul_sum]

omit [DecidableEq X] [N.Normal] in
/--
The finite-stage source Fox boundary is evaluated on the canonical generators and then extended
linearly to the finite-stage coordinate module.
-/
@[simp]
theorem foxAlgebraicStageSourceFoxBoundary_apply [Fintype X]
    (v : foxAlgebraicStageSourceCoordinateVector (X := X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n v =
      ∑ i : X,
        v i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of i)) - 1) :=
  rfl

/-- Apply the finite source-to-target group-algebra map coordinatewise. -/
def foxAlgebraicStageCoordinateSourceToTarget :
    foxAlgebraicStageSourceCoordinateVector (X := X) N n →ₗ[ModNCompletedCoeff n]
      foxAlgebraicStageCoordinateVector (X := X) N n where
  toFun v := fun i =>
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (v i)
  map_add' := by
    intro v w
    funext i
    simp only [Pi.add_apply, map_add]
  map_smul' := by
    intro a v
    funext i
    simp only [Pi.smul_apply, foxCommutatorPowerGroupAlgebraMap_smul, RingHom.id_apply]

omit [DecidableEq X] in
/--
The finite-stage source-to-target coordinate map is evaluated by applying the target quotient
map to the chosen coordinate.
-/
@[simp]
theorem foxAlgebraicStageCoordinateSourceToTarget_apply
    (v : foxAlgebraicStageSourceCoordinateVector (X := X) N n) (i : X) :
    foxAlgebraicStageCoordinateSourceToTarget (X := X) N n v i =
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (v i) :=
  rfl

omit [DecidableEq X] in
/-- The source boundary commutes with the source-to-target group-algebra map. -/
theorem foxAlgebraicStageFoxBoundary_coordinateSourceToTarget
    [Fintype X]
    (v : foxAlgebraicStageSourceCoordinateVector (X := X) N n) :
    foxAlgebraicStageFoxBoundary (X := X) N n
        (foxAlgebraicStageCoordinateSourceToTarget (X := X) N n v) =
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (foxAlgebraicStageSourceFoxBoundary (X := X) N n v) := by
  rw [foxAlgebraicStageFoxBoundary_apply, foxAlgebraicStageSourceFoxBoundary_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [foxAlgebraicStageCoordinateSourceToTarget_apply, RingHom.map_mul, map_sub, map_one,
    foxCommutatorPowerGroupAlgebraMap_of]

omit [DecidableEq X] in
/-- The finite-stage coordinatewise source-to-target map is surjective. -/
theorem foxAlgebraicStageCoordinateSourceToTarget_surjective :
    Function.Surjective (foxAlgebraicStageCoordinateSourceToTarget (X := X) N n) := by
  intro v
  have hcoord : ∀ i : X,
      ∃ a : foxAlgebraicStageSourceGroupAlgebra (X := X) N n,
        foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n a = v i := by
    intro i
    exact foxCommutatorPowerGroupAlgebraMap_surjective (X := X) N n (v i)
  choose a ha using hcoord
  refine ⟨a, ?_⟩
  funext i
  exact ha i

omit [DecidableEq X] in
/--
If a source coordinate vector lifts a target boundary cycle, then its source boundary lies in
the source-to-target group-algebra kernel.
-/
theorem foxAlgebraicStageSourceFoxBoundary_mem_groupAlgebraMapKernel_of_lift_cycle
    [Fintype X]
    {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    {a : foxAlgebraicStageSourceCoordinateVector (X := X) N n}
    (ha : foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a = v)
    (hv : v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n a ∈
      foxAlgebraicStageGroupAlgebraMapKernelIdeal (X := X) N n := by
  rw [mem_foxAlgebraicStageGroupAlgebraMapKernelIdeal]
  calc
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (foxAlgebraicStageSourceFoxBoundary (X := X) N n a) =
      foxAlgebraicStageFoxBoundary (X := X) N n
        (foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a) := by
        exact (foxAlgebraicStageFoxBoundary_coordinateSourceToTarget (X := X) N n a).symm
    _ = foxAlgebraicStageFoxBoundary (X := X) N n v := by
        rw [ha]
    _ = 0 := hv

omit [DecidableEq X] in
/--
If a source coordinate vector lifts a target boundary cycle, then its source boundary lies in
the explicit relation augmentation ideal.
-/
theorem foxAlgebraicStageSourceFoxBoundary_mem_relationAugmentationIdeal_of_lift_cycle
    [Fintype X]
    {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    {a : foxAlgebraicStageSourceCoordinateVector (X := X) N n}
    (ha : foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a = v)
    (hv : v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n) :
    foxAlgebraicStageSourceFoxBoundary (X := X) N n a ∈
      foxAlgebraicStageRelationAugmentationIdeal (X := X) N n := by
  rw [← foxAlgebraicStage_mem_groupAlgebraMapKernelIdeal_iff_relationAugmentationIdeal
    (X := X) (N := N) (n := n)]
  exact foxAlgebraicStageSourceFoxBoundary_mem_groupAlgebraMapKernel_of_lift_cycle
    (X := X) N n ha hv

omit [DecidableEq X] in
/--
Every finite target boundary cycle has a source-coordinate lift whose source boundary is in the
relation augmentation ideal.
-/
theorem exists_foxAlgebraicStageSourceCoordinate_lift_boundaryCycle_relationIdeal
    [Fintype X]
    (v : foxAlgebraicStageCoordinateVector (X := X) N n)
    (hv : v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n) :
    ∃ a : foxAlgebraicStageSourceCoordinateVector (X := X) N n,
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a = v ∧
        foxAlgebraicStageSourceFoxBoundary (X := X) N n a ∈
          foxAlgebraicStageRelationAugmentationIdeal (X := X) N n := by
  rcases foxAlgebraicStageCoordinateSourceToTarget_surjective (X := X) N n v with ⟨a, ha⟩
  exact ⟨a, ha,
    foxAlgebraicStageSourceFoxBoundary_mem_relationAugmentationIdeal_of_lift_cycle
      (X := X) N n ha hv⟩

/--
Source-boundary relation-ideal reduction: if every source coordinate vector whose source
boundary lies in the relation augmentation ideal projects to a relation-boundary vector, then
the finite-stage coordinate complex is exact.
-/
def foxAlgebraicStageSourceBoundaryRelationIdealReduction [Fintype X] : Prop :=
  ∀ a : foxAlgebraicStageSourceCoordinateVector (X := X) N n,
    foxAlgebraicStageSourceFoxBoundary (X := X) N n a ∈
      foxAlgebraicStageRelationAugmentationIdeal (X := X) N n →
      foxAlgebraicStageCoordinateSourceToTarget (X := X) N n a ∈
        foxAlgebraicStageRelationBoundarySubmodule (X := X) N n

/-- The source-boundary relation-ideal reduction implies finite-stage module exactness. -/
theorem foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
    [Fintype X]
    (hreduce : foxAlgebraicStageSourceBoundaryRelationIdealReduction (X := X) N n) :
    foxAlgebraicStageRelationBoundaryModuleExact (X := X) N n := by
  intro v hv
  rcases exists_foxAlgebraicStageSourceCoordinate_lift_boundaryCycle_relationIdeal
      (X := X) N n v hv with ⟨a, ha, hboundary⟩
  have hrel := hreduce a hboundary
  simpa [ha] using hrel

/-- The source-boundary relation-ideal reduction implies finite-stage coordinate coverage. -/
theorem foxAlgebraicStageBoundaryCyclesCovered_of_sourceBoundaryRelReduction
    [Fintype X]
    (hreduce : foxAlgebraicStageSourceBoundaryRelationIdealReduction (X := X) N n) :
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryModuleExact
    (X := X) N n
    (foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
      (X := X) N n hreduce)

/--
The source-boundary relation-ideal reduction gives injectivity of the finite quotient
obstruction boundary.
-/
theorem foxAlgebraicStageBoundaryModuloRelations_inj_of_sourceBoundaryRelReduction
    [Fintype X]
    (hreduce : foxAlgebraicStageSourceBoundaryRelationIdealReduction (X := X) N n) :
    Function.Injective (foxAlgebraicStageBoundaryModuloRelations (X := X) N n) :=
  foxAlgebraicStageBoundaryModuloRelations_injective_of_relationBoundaryModuleExact
    (X := X) N n
    (foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
      (X := X) N n hreduce)

/-- The source-boundary relation-ideal reduction gives the finite semidirect coverage statement. -/
theorem foxAlgebraicStageSemiBoundaryCyclesCovered_of_sourceBoundaryRelReduction
    [Fintype X]
    (hreduce : foxAlgebraicStageSourceBoundaryRelationIdealReduction (X := X) N n) :
    foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  (foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
    (X := X) (N := N) (n := n)).2
    (foxAlgebraicStageBoundaryCyclesCovered_of_sourceBoundaryRelReduction
      (X := X) N n hreduce)

end

end FoxDifferential
