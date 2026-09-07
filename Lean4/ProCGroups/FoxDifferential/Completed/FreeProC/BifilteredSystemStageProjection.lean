import ProCGroups.FoxDifferential.Completed.FreeProC.BifilteredStageProjection
import ProCGroups.FoxDifferential.Completed.FiniteStage.Bifiltered.InverseSystem

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — bifiltered system stage projection

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectBifilteredLimitMap`
  Assemble compatible completed-to-finite semidirect stage maps into a map to the bifiltered inverse
  limit.
- `freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps`
  The completed-to-finite stage maps built from a bifiltered-compatible family assemble into a map
  to the bifiltered finite Fox semidirect inverse limit.
- `freeProCZCCompletedFoxSemidirectBifilteredLimitMap_projection`
  Projection after the free pro-\(C\) \(\mathbb{Z}_C\)-completed Fox semidirect bifiltered limit map
  is computed by the finite-stage coordinate map.
- `freeProCZCCompletedFoxSemidirectBifilteredLimitMap_mem_boundaryCycleSet`
  A completed boundary-cycle point maps to a stagewise boundary-cycle point in the bifiltered
  inverse limit.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section BifilteredLimitMap

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]
variable (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
variable (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)

/--
Assemble compatible completed-to-finite semidirect stage maps into a map to the bifiltered
inverse limit.
-/
def freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn where
  toFun y :=
    ⟨fun j => π j y, by
      intro i j hij
      exact congrArg (fun f => f y) (hπ hij)⟩
  map_one' := by
    apply Subtype.ext
    funext j
    exact map_one (π j)
  map_mul' y z := by
    apply Subtype.ext
    funext j
    exact map_mul (π j) y z

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Projection after the free pro-\(C\) \(\mathbb{Z}_C\)-completed Fox semidirect bifiltered limit
map is computed by the finite-stage coordinate map.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMap_projection
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i)
    (j : J) (y : ZCCompletedFoxSemidirect C X H) :
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMap
          (C := C) (X := X) (H := H) Nstage nstage hN hn π hπ y) =
      π j y :=
  rfl

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
A completed boundary-cycle point maps to a stagewise boundary-cycle point in the bifiltered
inverse limit.
-/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMap_mem_boundaryCycleSet
    [Fintype X] (φ : X → H)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J, π j y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet
            (X := X) (Nstage j) (nstage j))
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMap
        (C := C) (X := X) (H := H) Nstage nstage hN hn π hπ y ∈
      foxAlgebraicStageBifilteredSemidirectLimitBoundaryCycleSet
        (X := X) Nstage nstage hN hn := by
  intro j
  change
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMap
          (C := C) (X := X) (H := H) Nstage nstage hN hn π hπ y) ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet
        (X := X) (Nstage j) (nstage j)
  rw [freeProCZCCompletedFoxSemidirectBifilteredLimitMap_projection]
  exact hboundary_stage y hy j

omit [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Kernel-word points commute with the bifiltered inverse-limit map. -/
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMap_kernelWordPoint
    (φ : X → H)
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j))
    (hπ : ∀ {i j : J} (hij : i ≤ j),
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp (π j) = π i)
    (hkernel_stage :
      ∀ j : J, ∀ w : FreeGroup X,
        π j (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectBifilteredLimitMap
        (C := C) (X := X) (H := H) Nstage nstage hN hn π hπ
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStageBifilteredSemidirectKernelWordPointLimit
        (X := X) Nstage nstage hN hn w := by
  apply Subtype.ext
  funext j
  exact hkernel_stage j w

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [∀ (j : J), Fact (0 < nstage j)] in
/--
Completed stage maps built from left/right coordinates commute with the bifiltered finite
transition whenever the left and right coordinate maps commute with that transition.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_bifilteredFamilyTransition
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft j (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    {i j : J} (hij : i ≤ j) :
    (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j)) =
    freeProCZCCompletedFoxSemidirectStageMap
      (C := C) (X := X) (H := H) (Nstage i) (nstage i)
      (stageLeft i) (stageRight i) (hscalar i) := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (C := C) (X := X) (H := H) (hN hij) (hn hij)
      (stageLeft j) (stageRight j) (hscalar j)
      (stageLeft i) (stageRight i) (hscalar i)
      (hleft hij) (hright hij)

/--
The completed-to-finite stage maps built from a bifiltered-compatible family assemble into a map
to the bifiltered finite Fox semidirect inverse limit.
-/
def freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft j (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  freeProCZCCompletedFoxSemidirectBifilteredLimitMap
    (C := C) (X := X) (H := H) Nstage nstage hN hn
    (fun j =>
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j))
    (fun hij =>
      freeProCZCCompletedFoxSemidirectStageMap_bifilteredFamilyTransition
        (C := C) (X := X) (H := H) Nstage nstage hN hn
        stageLeft stageRight hscalar hleft hright hij)

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)]
  [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
The stage-map part of the basis-element formula for the free pro-\(C\)
\(\mathbb{Z}_C\)-completed Fox semidirect bifiltered limit map is computed by the finite-stage
coordinate map.
-/
@[simp 900]
theorem freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps_projection
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft j (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hleft : ∀ {i j : J} (hij : i ≤ j),
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij)
          (stageLeft j v) = stageLeft i v)
    (hright : ∀ {i j : J} (hij : i ≤ j), ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) (stageRight j h) =
        stageRight i h)
    (j : J) (y : ZCCompletedFoxSemidirect C X H) :
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (freeProCZCCompletedFoxSemidirectBifilteredLimitMapOfStageMaps
          (C := C) (X := X) (H := H) Nstage nstage hN hn
          stageLeft stageRight hscalar hleft hright y) =
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j) y :=
  rfl

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/--
Bifiltered-compatible completed stage maps and the relation-ideal derivative theorem imply
completed density of algebraic kernel-word points.
-/
theorem boundaryCycles_subset_kernelClosure_of_biStageMaps
    [Fintype X] (φ : X → H)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft j (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (C := C) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
          foxAlgebraicStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  exact
    boundaryCycles_subset_kernelClosure_of_stageMaps
      (C := C) (X := X) (H := H) φ Nstage nstage stageLeft stageRight hscalar
      hidentity_basis stageBoundary hboundary hNstage_kernel hderivative

omit [Preorder J] [∀ (j : J), Fact (0 < nstage j)] in
/-- Closed-generated-target form of the bifiltered stage-map density theorem. -/
theorem boundaryCycles_subset_closedGenTarget_of_biStageMaps
    [Fintype X] (φ : X → H)
    (stageLeft : ∀ j : J,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) (Nstage j) (nstage j))
    (stageRight : ∀ j : J,
      H →* foxAlgebraicStageTargetQuotient (X := X) (Nstage j))
    (hscalar :
      ∀ j : J, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft j (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (nstage j))
            (foxAlgebraicStageTargetQuotient (X := X) (Nstage j)) (stageRight j h)) •
            stageLeft j v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun j : J =>
          freeProCZCCompletedFoxSemidirectStageMap
            (C := C) (X := X) (H := H) (Nstage j) (nstage j)
            (stageLeft j) (stageRight j) (hscalar j)))
    (stageBoundary : ∀ j : J,
      ZCCompletedGroupAlgebra C H →+
        foxAlgebraicStageTargetGroupAlgebra (X := X) (Nstage j) (nstage j))
    (hboundary :
      ∀ j : J,
        ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
          foxAlgebraicStageFoxBoundary (X := X) (Nstage j) (nstage j) (stageLeft j v) =
            stageBoundary j
              (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v))
    (hNstage_kernel :
      ∀ j : J, ∀ {w : FreeGroup X}, w ∈ Nstage j → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (boundaryCycles_subset_kernelClosure_of_biStageMaps
        (C := C) (X := X) (H := H) Nstage nstage φ
        stageLeft stageRight hscalar hidentity_basis stageBoundary hboundary
        hNstage_kernel hderivative)

end BifilteredLimitMap

end

end FoxDifferential
