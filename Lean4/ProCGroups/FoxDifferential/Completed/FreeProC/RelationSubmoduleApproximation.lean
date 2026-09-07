import ProCGroups.FoxDifferential.Completed.FreeProC.StageApproximation
import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationSubmodule
import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationIdealDerivative

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — relation submodule approximation

The principal declarations in this module are:

- `boundaryCycles_subset_kernelClosure_of_relSubmoduleExact`
  Completed Fox density from finite-stage relation-submodule exactness.
- `freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_relSubmodule_exact`
  The same finite relation-submodule input places completed boundary cycles in the closed generated
  Fox graph target.
- `boundaryCycles_subset_kernelClosure_of_sourceBoundaryReduction`
  Completed Fox density holds when, at every finite stage, every source-coordinate lift whose source
  boundary lies in the explicit relation augmentation ideal projects to a relation-boundary vector.
- `boundaryCycles_subset_closedGenTarget_of_sourceBoundaryReduction`
  The source-boundary relation-ideal route also places completed boundary cycles inside the
  closed-generated Fox graph target.
-/

namespace FoxDifferential

noncomputable section

universe u v

section CompletedFoxRelationSubmoduleExact

open scoped Topology

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [DecidableEq X]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Completed Fox density from finite-stage relation-submodule exactness. -/
theorem boundaryCycles_subset_kernelClosure_of_relSubmoduleExact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_module_exact :
      ∀ j : J,
        foxAlgebraicStageRelationBoundaryModuleExact
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_semi_exact
      (C := C) φ Nstage nstage π hbasis hboundary_stage ?_
      hNstage_kernel hkernel_word_projection
  intro j
  exact foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationBoundaryModuleExact
    (X := X) (Nstage j) (nstage j) (hstage_module_exact j)

/--
The same finite relation-submodule input places completed boundary cycles in the closed
generated Fox graph target.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_relSubmodule_exact
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_module_exact :
      ∀ j : J,
        foxAlgebraicStageRelationBoundaryModuleExact
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (boundaryCycles_subset_kernelClosure_of_relSubmoduleExact
        (C := C) φ Nstage nstage π hbasis hboundary_stage
        hstage_module_exact hNstage_kernel hkernel_word_projection)

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Completed Fox density holds when, at every finite stage, every source-coordinate lift whose
source boundary lies in the explicit relation augmentation ideal projects to a relation-boundary
vector.
-/
theorem boundaryCycles_subset_kernelClosure_of_sourceBoundaryReduction
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_reduce :
      ∀ j : J,
        foxAlgebraicStageSourceBoundaryRelationIdealReduction
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine
    boundaryCycles_subset_kernelClosure_of_relSubmoduleExact
      (C := C) φ Nstage nstage π hbasis hboundary_stage ?_
      hNstage_kernel hkernel_word_projection
  intro j
  exact foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
    (X := X) (Nstage j) (nstage j) (hstage_reduce j)

/--
The source-boundary relation-ideal route also places completed boundary cycles inside the
closed-generated Fox graph target.
-/
theorem boundaryCycles_subset_closedGenTarget_of_sourceBoundaryReduction
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hstage_reduce :
      ∀ j : J,
        foxAlgebraicStageSourceBoundaryRelationIdealReduction
          (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (boundaryCycles_subset_kernelClosure_of_sourceBoundaryReduction
        (C := C) φ Nstage nstage π hbasis hboundary_stage
        hstage_reduce hNstage_kernel hkernel_word_projection)



section
omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
/--
The finite-stage relation-ideal derivative theorem, quotient-kernel neighborhood basis, and
projection compatibility imply completed Fox density.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine
    boundaryCycles_subset_kernelClosure_of_sourceBoundaryReduction
      (C := C) φ Nstage nstage π hbasis hboundary_stage ?_
      hNstage_kernel hkernel_word_projection
  intro j
  exact foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_derivatives
    (X := X) (Nstage j) (nstage j)

end

/--
Completed boundary cycles lie in the closed-generated Fox graph target using the finite-stage
relation-ideal derivative theorem.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_finiteStage_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
              (X := X) (Nstage j) (nstage j))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hkernel_word_projection :
      ∀ j : J, ∀ w : FreeGroup X, w ∈ Nstage j →
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_relDeriv
        (C := C) φ Nstage nstage π hbasis hboundary_stage
        hNstage_kernel hkernel_word_projection)

end CompletedFoxRelationSubmoduleExact

end

end FoxDifferential
