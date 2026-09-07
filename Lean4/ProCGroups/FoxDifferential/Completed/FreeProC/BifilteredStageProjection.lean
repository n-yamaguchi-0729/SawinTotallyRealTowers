import ProCGroups.FoxDifferential.Completed.FreeProC.StageProjection
import ProCGroups.FoxDifferential.Completed.FiniteStage.Bifiltered.Transition
import ProCGroups.FoxDifferential.Completed.FiniteStage.Bifiltered.System
import ProCGroups.FoxDifferential.Completed.FiniteStage.Bifiltered.InverseSystem

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — bifiltered stage projection

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition`
  Compatibility of two completed-to-finite stage maps with the bifiltered finite transition.
  Equivalently, if the left completed coordinate maps commute with the combined coefficient/target
  transition and the right maps commute with \(F/N \to F/M\), then the two semidirect stage maps
  commute.
- `freeProCZCCompletedFoxSemidirectStageMap_mem_ker_of_bifilteredTransition`
  Kernel membership descends along a compatible bifiltered transition between completed stage maps.
- `freeProCZCFoxSemiStageMap_mem_boundaryCycleSet_of_bifilteredTransition`
  Bifiltered compatibility transports boundary-cycle preservation from a finer completed stage to a
  coarser completed stage.
- `freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint_of_bifilteredTransition`
  Bifiltered compatibility transports kernel-word point formulas from a finer completed stage to a
  coarser completed stage.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Fact (0 < n)] [Fact (0 < m)] in
/--
Compatibility of two completed-to-finite stage maps with the bifiltered finite transition.
Equivalently, if the left completed coordinate maps commute with the combined coefficient/target
transition and the right maps commute with \(F/N \to F/M\), then the two semidirect stage maps
commute.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
    (stageLeftN :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N m)
    (stageRightN : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftN (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) M n)
    (stageRightM : H →* foxAlgebraicStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftM (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h) :
    (foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm).comp
        (freeProCZCCompletedFoxSemidirectStageMap
          (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) =
      freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) M n stageLeftM stageRightM hscalarM := by
  apply MonoidHom.ext
  intro y
  apply FoxAlgebraicStageSemidirect.ext
  · change foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm
        (stageLeftN y.left) = stageLeftM y.left
    exact hleft y.left
  · change foxAlgebraicStageTargetQuotientMap (X := X) hNM (stageRightN y.right) =
      stageRightM y.right
    exact hright y.right

omit [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] [Fact (0 < n)] [Fact (0 < m)] in
/--
Kernel membership descends along a compatible bifiltered transition between completed stage
maps.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_mem_ker_of_bifilteredTransition
    (stageLeftN :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N m)
    (stageRightN : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftN (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) M n)
    (stageRightM : H →* foxAlgebraicStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftM (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h)
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN).ker) :
    y ∈ (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) M n stageLeftM stageRightM hscalarM).ker := by
  have hcomm :=
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (C := C) (X := X) (H := H) hNM hnm
      stageLeftN stageRightN hscalarN stageLeftM stageRightM hscalarM hleft hright
  have hyone :
      (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y = 1 := by
    simpa using hy
  have hy' :
      ((foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm).comp
        (freeProCZCCompletedFoxSemidirectStageMap
          (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN)) y = 1 := by
    change foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm
        ((freeProCZCCompletedFoxSemidirectStageMap
          (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y) = 1
    rw [hyone]
    exact map_one (foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm)
  change (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) M n stageLeftM stageRightM hscalarM) y = 1
  rw [← congrArg (fun f => f y) hcomm]
  exact hy'

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/--
Bifiltered compatibility transports boundary-cycle preservation from a finer completed stage to
a coarser completed stage.
-/
theorem freeProCZCFoxSemiStageMap_mem_boundaryCycleSet_of_bifilteredTransition
    [Fintype X]
    (stageLeftN :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N m)
    (stageRightN : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftN (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) M n)
    (stageRightM : H →* foxAlgebraicStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftM (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h)
    {y : ZCCompletedFoxSemidirect C X H}
    (hyN :
      (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y ∈
          foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N m) :
      (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) M n stageLeftM stageRightM hscalarM) y ∈
          foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) M n := by
  have hcomm :=
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (C := C) (X := X) (H := H) hNM hnm
      stageLeftN stageRightN hscalarN stageLeftM stageRightM hscalarM hleft hright
  rw [← congrArg (fun f => f y) hcomm]
  change foxAlgebraicStageSemidirectMap (X := X) hNM n
      (foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm
        ((freeProCZCCompletedFoxSemidirectStageMap
          (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN) y)) ∈
    foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) M n
  exact foxAlgebraicStageSemidirectMap_mem_boundaryCycleSet (X := X) hNM n
    (foxAlgebraicStageSemidirectCoeffMap_mem_boundaryCycleSet (X := X) N hnm hyN)

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
omit [Fact (0 < n)] [Fact (0 < m)] in
/--
Bifiltered compatibility transports kernel-word point formulas from a finer completed stage to a
coarser completed stage.
-/
theorem freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint_of_bifilteredTransition
    (φ : X → H)
    (stageLeftN :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N m)
    (stageRightN : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalarN :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftN (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff m)
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRightN h)) •
            stageLeftN v)
    (stageLeftM :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) M n)
    (stageRightM : H →* foxAlgebraicStageTargetQuotient (X := X) M)
    (hscalarM :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeftM (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) M) (stageRightM h)) •
            stageLeftM v)
    (hleft :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm (stageLeftN v) =
          stageLeftM v)
    (hright : ∀ h : H,
      foxAlgebraicStageTargetQuotientMap (X := X) hNM (stageRightN h) = stageRightM h)
    (hderivativeN :
      ∀ w : FreeGroup X,
        stageLeftN
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N m w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) M n stageLeftM stageRightM hscalarM
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) M n w := by
  have hcomm :=
    freeProCZCCompletedFoxSemidirectStageMap_bifilteredTransition
      (C := C) (X := X) (H := H) hNM hnm
      stageLeftN stageRightN hscalarN stageLeftM stageRightM hscalarM hleft hright
  rw [← congrArg
    (fun f => f (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w)) hcomm]
  change foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm
      (freeProCZCCompletedFoxSemidirectStageMap
        (C := C) (X := X) (H := H) N m stageLeftN stageRightN hscalarN
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w)) =
    foxAlgebraicStageSemidirectKernelWordPoint (X := X) M n w
  rw [freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
    (C := C) (X := X) (H := H) N m φ
    stageLeftN stageRightN hscalarN hderivativeN w]
  exact foxAlgebraicStageBifilteredSemidirectMap_kernelWordPoint (X := X) hNM hnm w

end

end FoxDifferential
