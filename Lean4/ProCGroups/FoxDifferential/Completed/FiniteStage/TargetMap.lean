import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.BoundaryCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — target map

The principal declarations in this module are:

- `foxAlgebraicStageSemidirectMap_left`
  The left coordinate of the finite-stage semidirect point is the specified derivative component.
- `foxAlgebraicStageSemidirectMap_right`
  The right coordinate of the finite-stage semidirect point is the corresponding quotient component.
- `foxAlgebraicStageFoxBoundary_targetMap`
  Target-quotient refinement commutes with the finite-stage Fox boundary.
- `foxAlgebraicStageBoundaryCycleSubmodule_targetMap_mem`
  Target-quotient refinement sends finite boundary cycles to finite boundary cycles.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M) (n : ℕ)

omit [DecidableEq X] in
/--
The left coordinate of the finite-stage semidirect point is the specified derivative component.
-/
@[simp]
theorem foxAlgebraicStageSemidirectMap_left
    (y : FoxAlgebraicStageSemidirect (X := X) N n) :
    (foxAlgebraicStageSemidirectMap (X := X) hNM n y).left =
      fun i : X => foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n (y.left i) :=
  rfl

omit [DecidableEq X] in
/--
The right coordinate of the finite-stage semidirect point is the corresponding quotient
component.
-/
@[simp]
theorem foxAlgebraicStageSemidirectMap_right
    (y : FoxAlgebraicStageSemidirect (X := X) N n) :
    (foxAlgebraicStageSemidirectMap (X := X) hNM n y).right =
      foxAlgebraicStageTargetQuotientMap (X := X) hNM y.right :=
  rfl

omit [DecidableEq X] in
/-- Target-quotient refinement commutes with the finite-stage Fox boundary. -/
theorem foxAlgebraicStageFoxBoundary_targetMap
    [Fintype X]
    (v : foxAlgebraicStageCoordinateVector (X := X) N n) :
    foxAlgebraicStageFoxBoundary (X := X) M n
        (fun i : X => foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n (v i)) =
      foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageFoxBoundary (X := X) N n v) := by
  rw [foxAlgebraicStageFoxBoundary_apply, foxAlgebraicStageFoxBoundary_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, map_sub, foxAlgebraicStageTargetGroupAlgebraMap_of, map_one]

omit [DecidableEq X] in
/-- Target-quotient refinement sends finite boundary cycles to finite boundary cycles. -/
theorem foxAlgebraicStageBoundaryCycleSubmodule_targetMap_mem
    [Fintype X]
    {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    (hv : v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n) :
    (fun i : X => foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n (v i)) ∈
      foxAlgebraicStageBoundaryCycleSubmodule (X := X) M n := by
  rw [mem_foxAlgebraicStageBoundaryCycleSubmodule]
  rw [foxAlgebraicStageFoxBoundary_targetMap (X := X) hNM n v]
  rw [mem_foxAlgebraicStageBoundaryCycleSubmodule] at hv
  rw [hv]
  exact map_zero _

omit [DecidableEq X] in
/-- Target-quotient refinement sends semidirect boundary-cycle points to boundary-cycle points. -/
theorem foxAlgebraicStageSemidirectMap_mem_boundaryCycleSet
    [Fintype X]
    {y : FoxAlgebraicStageSemidirect (X := X) N n}
    (hy : y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n) :
    foxAlgebraicStageSemidirectMap (X := X) hNM n y ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) M n := by
  rcases hy with ⟨hyright, hyboundary⟩
  constructor
  · rw [foxAlgebraicStageSemidirectMap_right]
    rw [hyright]
    exact map_one (foxAlgebraicStageTargetQuotientMap (X := X) hNM)
  · rw [foxAlgebraicStageSemidirectMap_left]
    exact foxAlgebraicStageBoundaryCycleSubmodule_targetMap_mem (X := X) hNM n hyboundary

/-- Target-quotient refinement sends finite kernel-word points to finite kernel-word points. -/
theorem foxAlgebraicStageSemidirectMap_kernelWordPoint
    (w : FreeGroup X) :
    foxAlgebraicStageSemidirectMap (X := X) hNM n
        (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) M n w := by
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    change foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageDerivative (X := X) N n i w) =
      foxAlgebraicStageDerivative (X := X) M n i w
    exact foxAlgebraicStageDerivative_natural (X := X) hNM n i w
  · rw [foxAlgebraicStageSemidirectMap_right]
    simp only [foxAlgebraicStageSemidirectKernelWordPoint, map_one]

/--
Target-quotient refinement sends finite source-kernel semidirect points to source-kernel
semidirect points.
-/
theorem foxAlgebraicStageSemidirectMap_sourceKernelPoint
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSemidirectMap (X := X) hNM n
        (foxAlgebraicStageSemidirectSourceKernelPoint (X := X) N n q) =
      foxAlgebraicStageSemidirectSourceKernelPoint (X := X) M n
        (foxAlgebraicStageSourceQuotientMap (X := X) hNM n q) := by
  rcases QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    change foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageQuotientDerivativeVector (X := X) N n
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) i) =
      foxAlgebraicStageQuotientDerivativeVector (X := X) M n
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) M n) w) i
    rw [foxAlgebraicStageQuotientDerivativeVector_mk, foxAlgebraicStageQuotientDerivativeVector_mk]
    exact foxAlgebraicStageDerivative_natural (X := X) hNM n i w
  · simp only [foxAlgebraicStageSemidirectSourceKernelPoint, QuotientGroup.mk'_apply,
  foxAlgebraicStageSemidirectMap_right, map_one]

/--
Target refinement sends the finite semidirect kernel-word derivative set into the refined one.
-/
theorem foxAlgebraicStageSemidirectMap_kernelWordDerivativeSet_subset :
    (fun y : FoxAlgebraicStageSemidirect (X := X) N n =>
        foxAlgebraicStageSemidirectMap (X := X) hNM n y) ''
      foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N n ⊆
        foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) M n := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨w, hwN, hzw⟩
  refine ⟨w, hNM hwN, ?_⟩
  rw [← hzw]
  exact (foxAlgebraicStageSemidirectMap_kernelWordPoint (X := X) hNM n w).symm

/-- Target refinement sends source-kernel derivative points into source-kernel derivative points. -/
theorem foxAlgebraicStageSemidirectMap_sourceKernelDerivativeSet_subset :
    (fun y : FoxAlgebraicStageSemidirect (X := X) N n =>
        foxAlgebraicStageSemidirectMap (X := X) hNM n y) ''
      foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n ⊆
        foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) M n := by
  rw [foxAlgebraicStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet (X := X) N n,
    foxAlgebraicStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet (X := X) M n]
  exact foxAlgebraicStageSemidirectMap_kernelWordDerivativeSet_subset (X := X) hNM n

end

end FoxDifferential
