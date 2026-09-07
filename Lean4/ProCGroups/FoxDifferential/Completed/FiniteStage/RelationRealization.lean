import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationSubmodule
import ProCGroups.FoxDifferential.Completed.FiniteStage.BoundarySubgroups

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — relation realization

The principal declarations in this module are:

- `foxAlgebraicStageSourceKernelDerivativeSet_zsmul_mem`
  The additive source-kernel derivative set is closed under integer multiples.
- `foxAlgebraicStageSourceKernelDerivativeSet_basis_smul_mem`
  The source-kernel derivative set is stable under multiplication by target-group basis
  coefficients. This is the finite algebraic form of conjugating a relation by a chosen lift of a
  target quotient element.
- `foxAlgebraicStageKernelWordDerivativeSet_basis_smul_mem`
  Word-level finite relation derivatives are stable under multiplication by target-group basis
  coefficients, after rewriting the source-kernel and word-level descriptions.
- `foxAlgebraicStageRelationBoundaryExact_of_relationBoundaryModuleExact`
  Module-level finite exactness gives function-level finite exactness for the relation boundary
  followed by the Fox boundary.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The additive source-kernel derivative set is closed under integer multiples. -/
theorem foxAlgebraicStageSourceKernelDerivativeSet_zsmul_mem
    (m : ℤ) {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    (hv : v ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n) :
    m • v ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n := by
  have hv' : v ∈ foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n := hv
  exact (foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n).zsmul_mem hv' m

/--
The source-kernel derivative set is stable under multiplication by target-group basis
coefficients. This is the finite algebraic form of conjugating a relation by a chosen lift of a
target quotient element.
-/
theorem foxAlgebraicStageSourceKernelDerivativeSet_basis_smul_mem
    (h : foxAlgebraicStageTargetQuotient (X := X) N)
    {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    (hv : v ∈ foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n) :
    (MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) h) • v ∈
      foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n := by
  have hvRange : v ∈ foxAlgebraicStageRelationBoundaryRange (X := X) N n := hv
  exact foxAlgebraicStageRelationBoundaryRange_basis_smul_mem (X := X) N n h hvRange

/--
Word-level finite relation derivatives are stable under multiplication by target-group basis
coefficients, after rewriting the source-kernel and word-level descriptions.
-/
theorem foxAlgebraicStageKernelWordDerivativeSet_basis_smul_mem
    (h : foxAlgebraicStageTargetQuotient (X := X) N)
    {v : foxAlgebraicStageCoordinateVector (X := X) N n}
    (hv : v ∈ foxAlgebraicStageKernelWordDerivativeSet (X := X) N n) :
    (MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) h) • v ∈
      foxAlgebraicStageKernelWordDerivativeSet (X := X) N n := by
  rw [← foxAlgebraicStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet (X := X) N n]
  rw [← foxAlgebraicStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet (X := X) N n] at hv
  exact foxAlgebraicStageSourceKernelDerivativeSet_basis_smul_mem (X := X) N n h hv

/--
Module-level finite exactness gives function-level finite exactness for the relation boundary
followed by the Fox boundary.
-/
theorem foxAlgebraicStageRelationBoundaryExact_of_relationBoundaryModuleExact
    [Fintype X]
    (hexact : foxAlgebraicStageRelationBoundaryModuleExact (X := X) N n) :
    foxAlgebraicStageRelationBoundaryExact (X := X) N n :=
  foxAlgebraicStageRelationBoundaryExact_of_boundaryCyclesCoveredBySourceKernel
    (X := X) N n
    (foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryModuleExact
      (X := X) N n hexact)

/-- Module-level finite exactness gives finite semidirect coverage of boundary cycles (v,1). -/
theorem foxAlgebraicStageSemiBoundaryCyclesCovered_of_relBoundaryModuleExact
    [Fintype X]
    (hexact : foxAlgebraicStageRelationBoundaryModuleExact (X := X) N n) :
    foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel (X := X) N n :=
  (foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
    (X := X) (N := N) (n := n)).2
    (foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryModuleExact
      (X := X) N n hexact)


end

end FoxDifferential
