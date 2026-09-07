import ProCGroups.FoxDifferential.Completed.FiniteStage.SemidirectCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — boundary subgroups

The principal declarations in this module are:

- `foxAlgebraicStageSemidirectBoundaryCycleSubgroup`
  Finite semidirect boundary cycles form a subgroup.
- `foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup`
  Finite source-kernel derivative semidirect points form a subgroup.
- `foxAlgebraicStageSemidirectBoundaryCycleSubgroup_coe`
  The boundary-cycle subgroup of the finite Fox semidirect product has the boundary-cycle set as its
  underlying set.
- `foxAlgebraicStageSemidirectSourceKernelDerivativeSet_iff`
  Source-kernel semidirect points are exactly points with right component \(1\) and left component
  in the source-kernel derivative subgroup.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Finite semidirect boundary cycles form a subgroup. -/
def foxAlgebraicStageSemidirectBoundaryCycleSubgroup [Fintype X] :
    Subgroup (FoxAlgebraicStageSemidirect (X := X) N n) where
  carrier := foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n
  one_mem' := by
    constructor
    · simp only [FoxAlgebraicStageSemidirect.one_right]
    · exact (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n).zero_mem
  mul_mem' := by
    intro y z hy hz
    rcases hy with ⟨hyright, hyleft⟩
    rcases hz with ⟨hzright, hzleft⟩
    constructor
    · simp only [FoxAlgebraicStageSemidirect.mul_right, hyright, hzright, mul_one]
    · rw [FoxAlgebraicStageSemidirect.mul_left, hyright]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) 1 :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        exact map_one
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N))
      rw [hone, one_smul]
      exact (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n).add_mem hyleft hzleft
  inv_mem' := by
    intro y hy
    rcases hy with ⟨hyright, hyleft⟩
    constructor
    · simp only [FoxAlgebraicStageSemidirect.inv_right, hyright, inv_one]
    · rw [FoxAlgebraicStageSemidirect.inv_left, hyright, inv_one]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) 1 :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        exact map_one
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N))
      rw [hone, one_smul]
      exact (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n).neg_mem hyleft

omit [DecidableEq X] in
/--
The boundary-cycle subgroup of the finite Fox semidirect product has the boundary-cycle set as
its underlying set.
-/
@[simp]
theorem foxAlgebraicStageSemidirectBoundaryCycleSubgroup_coe [Fintype X] :
    ((foxAlgebraicStageSemidirectBoundaryCycleSubgroup (X := X) N n :
        Subgroup (FoxAlgebraicStageSemidirect (X := X) N n)) :
          Set (FoxAlgebraicStageSemidirect (X := X) N n)) =
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n :=
  rfl

/--
Source-kernel semidirect points are exactly points with right component \(1\) and left component
in the source-kernel derivative subgroup.
-/
theorem foxAlgebraicStageSemidirectSourceKernelDerivativeSet_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {y : FoxAlgebraicStageSemidirect (X := X) N n} :
    y ∈ foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n ↔
      y.right = 1 ∧
        y.left ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n := by
  constructor
  · rintro ⟨q, hq, hqy⟩
    rw [← hqy]
    exact ⟨rfl, ⟨q, hq, rfl⟩⟩
  · rintro ⟨hyright, q, hq, hqleft⟩
    refine ⟨q, hq, ?_⟩
    apply FoxAlgebraicStageSemidirect.ext
    · exact hqleft
    · simpa [foxAlgebraicStageSemidirectSourceKernelPoint] using hyright.symm

/-- Finite source-kernel derivative semidirect points form a subgroup. -/
def foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup :
    Subgroup (FoxAlgebraicStageSemidirect (X := X) N n) where
  carrier :=
    { y | y.right = 1 ∧
        y.left ∈ foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n }
  one_mem' := by
    exact ⟨rfl, (foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n).zero_mem⟩
  mul_mem' := by
    intro y z hy hz
    rcases hy with ⟨hyright, hyleft⟩
    rcases hz with ⟨hzright, hzleft⟩
    constructor
    · simp only [FoxAlgebraicStageSemidirect.mul_right, hyright, hzright, mul_one]
    · rw [FoxAlgebraicStageSemidirect.mul_left, hyright]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) 1 :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        exact map_one
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N))
      rw [hone, one_smul]
      exact
        (foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n).add_mem hyleft hzleft
  inv_mem' := by
    intro y hy
    rcases hy with ⟨hyright, hyleft⟩
    constructor
    · simp only [FoxAlgebraicStageSemidirect.inv_right, hyright, inv_one]
    · rw [FoxAlgebraicStageSemidirect.inv_left, hyright, inv_one]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) 1 :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        exact map_one
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N))
      rw [hone, one_smul]
      exact (foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n).neg_mem hyleft

/--
The finite-stage semidirect source-kernel derivative subgroup coerces to its defining carrier.
-/
@[simp]
theorem foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup_coe :
    ((foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
        Subgroup (FoxAlgebraicStageSemidirect (X := X) N n)) :
          Set (FoxAlgebraicStageSemidirect (X := X) N n)) =
      foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n :=
  by
    ext y
    change
      (y.right = 1 ∧
          y.left ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n) ↔
        y ∈ foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n
    exact (foxAlgebraicStageSemidirectSourceKernelDerivativeSet_iff
      (X := X) (N := N) (n := n)).symm

/-- The finite source-kernel derivative subgroup lies inside finite semidirect boundary cycles. -/
theorem foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup_le_boundaryCycleSubgroup
    [Fintype X] :
    foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n ≤
      foxAlgebraicStageSemidirectBoundaryCycleSubgroup (X := X) N n := by
  intro y hy
  have hyset :
      y ∈ foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n := by
    have hy' :
        y ∈ ((foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
          Subgroup (FoxAlgebraicStageSemidirect (X := X) N n)) :
            Set (FoxAlgebraicStageSemidirect (X := X) N n)) := hy
    rw [foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup_coe (X := X) N n] at hy'
    exact hy'
  exact foxAlgebraicStageSemidirectSourceKernelDerivativeSet_subset_boundaryCycleSet
    (X := X) N n hyset

/-- Semidirect finite-stage coverage is equivalently subgroup inclusion. -/
theorem foxAlgebraicStageSemiBoundaryCycleSubgroup_le_sourceKernelDerivSubgroup_iff_coord
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageSemidirectBoundaryCycleSubgroup (X := X) N n ≤
        foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n ↔
      foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro hsub
    exact
      (foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
        (X := X) (N := N) (n := n)).1
        (by
          intro y hy
          have hy' : y ∈ foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :=
            hsub hy
          have hyset :
              y ∈ ((foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
                Subgroup (FoxAlgebraicStageSemidirect (X := X) N n)) :
                  Set (FoxAlgebraicStageSemidirect (X := X) N n)) := hy'
          rw [foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup_coe (X := X) N n] at hyset
          exact hyset)
  · intro hcoord y hy
    have hyset :
        y ∈ foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n :=
      (foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
        (X := X) (N := N) (n := n)).2
        hcoord hy
    change
      y ∈ ((foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup (X := X) N n :
        Subgroup (FoxAlgebraicStageSemidirect (X := X) N n)) :
          Set (FoxAlgebraicStageSemidirect (X := X) N n))
    rw [foxAlgebraicStageSemidirectSourceKernelDerivativeSubgroup_coe (X := X) N n]
    exact hyset

end

end FoxDifferential
