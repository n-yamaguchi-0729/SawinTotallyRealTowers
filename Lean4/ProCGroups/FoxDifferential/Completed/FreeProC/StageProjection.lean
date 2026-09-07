import ProCGroups.FoxDifferential.Completed.FreeProC.RelationSubmoduleApproximation
import ProCGroups.FoxDifferential.Completed.FreeProC.QuotientKernelBasis

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — stage projection

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectStageMap`
  A semidirect projection from the completed Fox semidirect product to a finite Fox stage,
  constructed from a left coordinate map and a right target quotient map. The only compatibility
  required is that the left coordinate map respects the scalar action used in semidirect
  multiplication. This is the abstract form of the finite quotient map \(\mathbb{Z}_C\llbracket
  H\rrbracket^{X} \rtimes H \to ((\mathbb{Z}/n\mathbb{Z})[F/N])^X \rtimes F/N\).
- `freeProCZCCompletedFoxSemidirectStageMap_left`
  The left component of the completed-to-finite semidirect stage map is the prescribed finite Fox
  coordinate projection.
- `freeProCZCCompletedFoxSemidirectStageMap_right`
  The right coordinate of the completed Fox semidirect stage map is the selected target quotient
  map.
- `freeProCZCCompletedFoxSemidirectStageMap_mem_ker_iff`
  Membership in the kernel of the completed Fox semidirect stage map is equivalent to vanishing of
  the corresponding finite-stage coordinate.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section CompletedFiniteStageMap

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/--
A semidirect projection from the completed Fox semidirect product to a finite Fox stage,
constructed from a left coordinate map and a right target quotient map. The only compatibility
required is that the left coordinate map respects the scalar action used in semidirect
multiplication. This is the abstract form of the finite quotient map \(\mathbb{Z}_C\llbracket
H\rrbracket^{X} \rtimes H \to ((\mathbb{Z}/n\mathbb{Z})[F/N])^X \rtimes F/N\).
-/
def freeProCZCCompletedFoxSemidirectStageMap
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageSemidirect (X := X) N n where
  toFun y :=
    { left := stageLeft y.left
      right := stageRight y.right }
  map_one' := by
    apply FoxAlgebraicStageSemidirect.ext
    · change stageLeft 0 = 0
      exact map_zero stageLeft
    · exact map_one stageRight
  map_mul' a b := by
    apply FoxAlgebraicStageSemidirect.ext
    · change
        stageLeft (a.left + zcGroupLike C H a.right • b.left) =
          stageLeft a.left +
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight a.right)) •
              stageLeft b.left
      rw [map_add, hscalar]
    · change stageRight (a.right * b.right) = stageRight a.right * stageRight b.right
      exact map_mul stageRight a.right b.right

omit [DecidableEq X] in
/--
The left component of the completed-to-finite semidirect stage map is the prescribed finite Fox
coordinate projection.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectStageMap_left
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectStageMap
      (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar y).left =
      stageLeft y.left :=
  rfl

omit [DecidableEq X] in
/--
The right coordinate of the completed Fox semidirect stage map is the selected target quotient
map.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectStageMap_right
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectStageMap
      (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar y).right =
      stageRight y.right :=
  rfl

omit [DecidableEq X] in
/--
Membership in the kernel of the completed Fox semidirect stage map is equivalent to vanishing of
the corresponding finite-stage coordinate.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_mem_ker_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n}
    {stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N}
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    {y : ZCCompletedFoxSemidirect C X H} :
    y ∈ (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar).ker ↔
      stageLeft y.left = 0 ∧ stageRight y.right = 1 := by
  constructor
  · intro hy
    change
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar y = 1 at hy
    have hleft := congrArg (fun z : FoxAlgebraicStageSemidirect (X := X) N n => z.left) hy
    have hright := congrArg (fun z : FoxAlgebraicStageSemidirect (X := X) N n => z.right) hy
    exact ⟨by simpa using hleft, by simpa using hright⟩
  · rintro ⟨hleft, hright⟩
    change
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar y = 1
    apply FoxAlgebraicStageSemidirect.ext
    · simpa using hleft
    · simpa using hright

omit [DecidableEq X] in
/--
A completed boundary-cycle point projects to a finite boundary-cycle point once the left
coordinate projection commutes with the source-shaped Fox boundary.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
    [Fintype X]
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (stageBoundary :
      ZCCompletedGroupAlgebra C H →+
        foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    (hboundary :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageFoxBoundary (X := X) N n (stageLeft v) =
          stageBoundary
            (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v))
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ) :
    freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar y ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n := by
  rcases hy with ⟨hyright, hyboundary⟩
  constructor
  · change stageRight y.right = 1
    rw [hyright]
    exact map_one stageRight
  · rw [mem_foxAlgebraicStageBoundaryCycleSubmodule]
    calc
      foxAlgebraicStageFoxBoundary (X := X) N n
          ((freeProCZCCompletedFoxSemidirectStageMap
            (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar y).left)
          = foxAlgebraicStageFoxBoundary (X := X) N n (stageLeft y.left) := rfl
      _ = stageBoundary
            (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) y.left) :=
          hboundary y.left
      _ = 0 := by
          rw [hyboundary]
          exact map_zero stageBoundary

/--
The stage map sends the completed kernel-word point \((D w, 1)\) to the corresponding finite
kernel-word point, provided the left coordinate projection commutes with Fox derivatives.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N n w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w := by
  apply FoxAlgebraicStageSemidirect.ext
  · change
      stageLeft
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
        foxAlgebraicStageDerivativeVector (X := X) N n w
    exact hderivative w
  · simp only [freeProCZCCompletedFoxSemidirectKernelWordPoint,
      freeProCZCCompletedFoxSemidirectStageMap_right,
  map_one, foxAlgebraicStageSemidirectKernelWordPoint]

/--
The stage map sends a completed graph-word point \((D w,\varphi(w))\) to the corresponding
finite stage graph point.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N n w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectGraphWordPoint (C := C) φ w) =
      ({ left := foxAlgebraicStageDerivativeVector (X := X) N n w,
         right := stageRight (FreeGroup.lift φ w) } :
        FoxAlgebraicStageSemidirect (X := X) N n) := by
  apply FoxAlgebraicStageSemidirect.ext
  · exact hderivative w
  · rfl

/--
If a word is in the finite-stage relation subgroup, the stage image of its completed graph point
is the finite kernel-word point.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint_of_stage_kernel
    (φ : X → H)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N n)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N n w)
    (hright_word :
      ∀ w : FreeGroup X, stageRight (FreeGroup.lift φ w) = QuotientGroup.mk' N w)
    (w : FreeGroup X) (hw : w ∈ N) :
    freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N n stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectGraphWordPoint (C := C) φ w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w := by
  rw [freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint
    (C := C) (X := X) (H := H) N n φ stageLeft stageRight hscalar hderivative w]
  apply FoxAlgebraicStageSemidirect.ext
  · rfl
  · change stageRight (FreeGroup.lift φ w) = 1
    rw [hright_word w]
    exact (QuotientGroup.eq_one_iff (N := N) w).2 hw

end CompletedFiniteStageMap

section StageMapDensityRoute

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Completed Fox density from concrete completed-to-finite semidirect stage maps, using
finite-stage relation-ideal derivative exactness and the boundary and derivative projection
formulas.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stageMaps_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
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
  let π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j) :=
    fun j =>
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j)
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_finiteStage_relDeriv
      (C := C) φ Nstage nstage π ?_ ?_ hNstage_kernel ?_
  · exact hquotient_basis
  · intro y hy j
    exact
      freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (stageBoundary j)
        (hboundary j) hy
  · intro j w hw
    exact
      freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (hderivative j) w

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Completed graph-word density for concrete completed-to-finite semidirect stage maps, without
requiring finite-stage relation words to be genuine kernel words for \(\varphi\). -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_stageMaps_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
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
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ) := by
  let π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j) :=
    fun j =>
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j)
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_finiteStage_semi_exact
      (C := C) φ Nstage nstage π ?_ ?_ ?_ ?_
  · exact hquotient_basis
  · intro y hy j
    exact
      freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (stageBoundary j)
        (hboundary j) hy
  · intro j
    exact foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_of_relationIdeal_derivatives
      (X := X) (Nstage j) (nstage j)
  · intro j w hw
    exact
      freeProCZCCompletedFoxSemidirectStageMap_graphWordPoint_of_stage_kernel
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        φ (stageLeft j) (stageRight j) (hscalar j) (hderivative j)
        (hright_word j) w hw

/-- Concrete stage-map graph-word density, phrased as closed-generated-target membership. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_stageMaps_graphRelDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
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
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
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
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_stageMaps_relDeriv
        (C := C) φ Nstage nstage stageLeft stageRight hscalar hquotient_basis
        stageBoundary hboundary hright_word hderivative)

/--
The same concrete stage-map route, with the conclusion phrased as membership in the
closed-generated Fox graph target.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_stageMaps_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
    (hquotient_basis :
      HasLeftQuotientKernelNeighbourhoodBasis
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
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stageMaps_relDeriv
        (C := C) φ Nstage nstage stageLeft stageRight hscalar hquotient_basis
        stageBoundary hboundary hNstage_kernel hderivative)


/--
Stage-map density is formulated using identity-neighborhood kernels rather than left-coset
kernels. This is the topological form produced by separation through finite quotients in
profinite groups. The conversion to the left-coset closure basis is performed internally.
-/
theorem boundaryCycles_subset_kernelClosure_of_stageMaps
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_stageMaps_relDeriv
      (C := C) φ Nstage nstage stageLeft stageRight hscalar ?_
      stageBoundary hboundary hNstage_kernel hderivative
  exact HasIdentityQuotientKernelNeighbourhoodBasis.to_left
    (Y := ZCCompletedFoxSemidirect C X H)
    (π := fun j : J =>
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j))
    hidentity_basis

/-- Graph-word density using identity-neighborhood kernels rather than left-coset kernels. -/
theorem boundaryCycles_subset_graphWordClosure_of_stageMaps
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
    (hderivative :
      ∀ j : J, ∀ w : FreeGroup X,
        stageLeft j
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) (Nstage j) (nstage j) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectGraphWordSet (C := C) φ) := by
  refine
    freeProCZCFoxBoundaryCycles_subset_closure_graphWordSet_of_stageMaps_relDeriv
      (C := C) φ Nstage nstage stageLeft stageRight hscalar ?_
      stageBoundary hboundary hright_word hderivative
  exact HasIdentityQuotientKernelNeighbourhoodBasis.to_left
    (Y := ZCCompletedFoxSemidirect C X H)
    (π := fun j : J =>
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) (Nstage j) (nstage j)
        (stageLeft j) (stageRight j) (hscalar j))
    hidentity_basis

/-- Closed-generated-target version of the identity-kernel graph-word stage-map theorem. -/
theorem boundaryCycles_subset_closedGenTarget_of_stageGraph
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
    (hright_word :
      ∀ j : J, ∀ w : FreeGroup X,
        stageRight j (FreeGroup.lift φ w) = QuotientGroup.mk' (Nstage j) w)
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
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_graphWord_density (C := C) φ
      (boundaryCycles_subset_graphWordClosure_of_stageMaps
        (C := C) φ Nstage nstage stageLeft stageRight hscalar hidentity_basis
        stageBoundary hboundary hright_word hderivative)

/-- Closed-generated-target version of the identity-kernel stage-map density theorem. -/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_stageMaps_identityKernel_relDeriv
    [Fintype X] (φ : X → H)
    {J : Type v}
    (Nstage : J → Subgroup (FreeGroup X))
    [∀ j, (Nstage j).Normal]
    (nstage : J → ℕ)
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
      (boundaryCycles_subset_kernelClosure_of_stageMaps
        (C := C) φ Nstage nstage stageLeft stageRight hscalar hidentity_basis
        stageBoundary hboundary hNstage_kernel hderivative)

end StageMapDensityRoute

end

end FoxDifferential
