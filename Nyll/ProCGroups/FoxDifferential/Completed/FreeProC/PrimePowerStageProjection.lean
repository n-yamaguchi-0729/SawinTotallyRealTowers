/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.StageProjection
import Nyll.ProCGroups.FoxDifferential.Completed.FreeProC.CofinalQuotientKernelBasis
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Semidirect

/-!
# Fox differential: completed — free pro-\(C\) — prime power stage projection

The principal declarations in this module are:

- `freeProCZCCompletedFoxSemidirectPrimePowerStageMap`
  A completed Fox semidirect projection to the \(\ell^a\) finite stage.
- `freeProCZCCompletedFoxSemidirectPrimePowerLimitMap`
  Assemble compatible prime-power stage maps into a map to the inverse limit of finite semidirect
  stages.
- `freeProCZCCompletedFoxSemidirectPrimePowerStageMap_left`
  The left component of the prime-power finite-stage semidirect map is the prescribed coordinate map
  applied to the source component.
- `freeProCZCCompletedFoxSemidirectPrimePowerStageMap_right`
  The right coordinate of the prime-power completed Fox semidirect stage map is the selected target
  quotient map.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.ProC

universe u v

section PrimePowerStageMaps

variable {C : ProCGroups.FiniteGroupClass}
variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]
variable (N : Subgroup (FreeGroup X)) [N.Normal]

/-- A completed Fox semidirect projection to the \(\ell^a\) finite stage. -/
def freeProCZCCompletedFoxSemidirectPrimePowerStageMap
    (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a) :=
  freeProCZCCompletedFoxSemidirectStageMap
    (C := C) (X := X) (H := H) N (ℓ ^ a) stageLeft stageRight hscalar

omit [Fact (0 < ℓ)] [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
    [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
The left component of the prime-power finite-stage semidirect map is the prescribed coordinate
map applied to the source component.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_left
    (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectPrimePowerStageMap
      (C := C) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar y).left =
      stageLeft y.left :=
  rfl

omit [Fact (0 < ℓ)] [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
    [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
The right coordinate of the prime-power completed Fox semidirect stage map is the selected
target quotient map.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_right
    (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (y : ZCCompletedFoxSemidirect C X H) :
    (freeProCZCCompletedFoxSemidirectPrimePowerStageMap
      (C := C) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar y).right =
      stageRight y.right :=
  rfl

omit [Fact (0 < ℓ)] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
omit [DecidableEq X] in
/-- Boundary-cycle preservation for a prime-power completed-to-finite stage map. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_mem_finiteBoundaryCycleSet
    [Fintype X]
    (φ : X → H) (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (stageBoundary :
      ZCCompletedGroupAlgebra C H →+
        foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
    (hboundary :
      ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
        foxAlgebraicStageFoxBoundary (X := X) N (ℓ ^ a) (stageLeft v) =
          stageBoundary
            (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v))
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ) :
    freeProCZCCompletedFoxSemidirectPrimePowerStageMap
        (C := C) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar y ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_mem_finiteBoundaryCycleSet
      (C := C) (X := X) (H := H) N (ℓ ^ a) φ
      stageLeft stageRight hscalar stageBoundary hboundary hy

omit [Fact (0 < ℓ)] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
/-- Kernel-word points project to kernel-word points at prime-power finite stages. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerStageMap_kernelWordPoint
    (φ : X → H) (a : ℕ)
    (stageLeft :
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ (h : H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h)) •
            stageLeft v)
    (hderivative :
      ∀ w : FreeGroup X,
        stageLeft
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N (ℓ ^ a) w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectPrimePowerStageMap
        (C := C) (X := X) (H := H) ℓ N a stageLeft stageRight hscalar
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w := by
  exact
    freeProCZCCompletedFoxSemidirectStageMap_kernelWordPoint
      (C := C) (X := X) (H := H) N (ℓ ^ a) φ
      stageLeft stageRight hscalar hderivative w

/--
Assemble compatible prime-power stage maps into a map to the inverse limit of finite semidirect
stages.
-/
def freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a) :
    ZCCompletedFoxSemidirect C X H →*
      FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N where
  toFun y :=
    ⟨fun a => π a y, by
      intro a b hab
      exact congrArg (fun f => f y) (hπ hab)⟩
  map_one' := by
    apply Subtype.ext
    funext a
    exact map_one (π a)
  map_mul' y z := by
    apply Subtype.ext
    funext a
    exact map_mul (π a) y z

omit [Fact (0 < ℓ)] [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
    [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Projection after the free pro-\(C\) \(\mathbb{Z}_C\)-completed Fox semidirect prime-power limit
map is computed by the finite-stage coordinate map.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_projection
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a)
    (a : ℕ) (y : ZCCompletedFoxSemidirect C X H) :
    foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a
        (freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
          (C := C) (X := X) (H := H) ℓ N π hπ y) =
      π a y :=
  rfl

omit [Fact (0 < ℓ)] [DecidableEq X] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
    [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
A completed boundary-cycle point maps to a stagewise boundary-cycle point in the prime-power
inverse limit.
-/
theorem freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_mem_boundaryCycleSet
    [Fintype X] (φ : X → H)
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a)
    (hboundary_stage :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ a : ℕ, π a y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a))
    {y : ZCCompletedFoxSemidirect C X H}
    (hy : y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ) :
    freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
        (C := C) (X := X) (H := H) ℓ N π hπ y ∈
      foxAlgebraicStagePrimePowerSemidirectLimitBoundaryCycleSet (ℓ := ℓ) (X := X) N := by
  intro a
  change
    foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a
        (freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
          (C := C) (X := X) (H := H) ℓ N π hπ y) ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a)
  rw [freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_projection]
  exact hboundary_stage y hy a

omit [Fact (0 < ℓ)] [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
/-- Kernel-word points commute with the prime-power inverse-limit map. -/
theorem freeProCZCCompletedFoxSemidirectPrimePowerLimitMap_kernelWordPoint
    (φ : X → H)
    (π : ∀ a : ℕ,
      ZCCompletedFoxSemidirect C X H →*
        FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a))
    (hπ : ∀ {a b : ℕ} (hab : a ≤ b),
      (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp (π b) =
        π a)
    (hkernel_word_projection :
      ∀ a : ℕ, ∀ w : FreeGroup X,
        π a (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
          foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w)
    (w : FreeGroup X) :
    freeProCZCCompletedFoxSemidirectPrimePowerLimitMap
        (C := C) (X := X) (H := H) ℓ N π hπ
        (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w) =
      foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit (ℓ := ℓ) (X := X) N w := by
  apply Subtype.ext
  funext a
  exact hkernel_word_projection a w

omit [Fact (0 < ℓ)] in
/--
Completed Fox density from prime-power stage maps and the finite relation-ideal derivative
theorem.
-/
theorem boundaryCycles_subset_kernelClosure_of_ppStageMaps
    [Fintype X] (φ : X → H)
    (stageLeft : ∀ a : ℕ,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : ∀ _a : ℕ,
      H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ a : ℕ, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft a (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight a h)) •
            stageLeft a v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun a : ℕ =>
          freeProCZCCompletedFoxSemidirectPrimePowerStageMap
            (C := C) (X := X) (H := H) ℓ N a
            (stageLeft a) (stageRight a) (hscalar a)))
    (stageBoundary : ∀ a : ℕ,
      ZCCompletedGroupAlgebra C H →+
        foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
    (hboundary :
      ∀ a : ℕ,
        ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
          foxAlgebraicStageFoxBoundary (X := X) N (ℓ ^ a) (stageLeft a v) =
            stageBoundary a
              (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v))
    (hN_kernel : ∀ {w : FreeGroup X}, w ∈ N → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ a : ℕ, ∀ w : FreeGroup X,
        stageLeft a
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N (ℓ ^ a) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine
    boundaryCycles_subset_kernelClosure_of_stageMaps
      (C := C) φ (fun _ : ℕ => N) (fun a : ℕ => ℓ ^ a)
      stageLeft stageRight hscalar ?_ stageBoundary hboundary ?_ hderivative
  · simpa [freeProCZCCompletedFoxSemidirectPrimePowerStageMap] using hidentity_basis
  · intro _ w hw
    exact hN_kernel hw

omit [Fact (0 < ℓ)] in
/-- Closed-generated-target version of the prime-power stage-map density theorem. -/
theorem boundaryCycles_subset_closedGenTarget_of_ppStageMaps
    [Fintype X] (φ : X → H)
    (stageLeft : ∀ a : ℕ,
      ZCFreeFoxCoordinates C (X := X) (H := H) →+
        foxAlgebraicStageCoordinateVector (X := X) N (ℓ ^ a))
    (stageRight : ∀ _a : ℕ,
      H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hscalar :
      ∀ a : ℕ, ∀ (h : H)
        (v : ZCFreeFoxCoordinates C (X := X) (H := H)),
        stageLeft a (zcGroupLike C H h • v) =
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight a h)) •
            stageLeft a v)
    (hidentity_basis :
      HasIdentityQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H)
        (fun a : ℕ =>
          freeProCZCCompletedFoxSemidirectPrimePowerStageMap
            (C := C) (X := X) (H := H) ℓ N a
            (stageLeft a) (stageRight a) (hscalar a)))
    (stageBoundary : ∀ a : ℕ,
      ZCCompletedGroupAlgebra C H →+
        foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
    (hboundary :
      ∀ a : ℕ,
        ∀ v : ZCFreeFoxCoordinates C (X := X) (H := H),
          foxAlgebraicStageFoxBoundary (X := X) N (ℓ ^ a) (stageLeft a v) =
            stageBoundary a
              (zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v))
    (hN_kernel : ∀ {w : FreeGroup X}, w ∈ N → FreeGroup.lift φ w = 1)
    (hderivative :
      ∀ a : ℕ, ∀ w : FreeGroup X,
        stageLeft a
          (zcFreeGroupFoxDerivativeVector C
            (FreeGroup.lift φ) w) =
          foxAlgebraicStageDerivativeVector (X := X) N (ℓ ^ a) w) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (boundaryCycles_subset_kernelClosure_of_ppStageMaps
        (C := C) (X := X) (H := H) ℓ N φ
        stageLeft stageRight hscalar hidentity_basis stageBoundary hboundary hN_kernel
        hderivative)

end PrimePowerStageMaps

end

end FoxDifferential
