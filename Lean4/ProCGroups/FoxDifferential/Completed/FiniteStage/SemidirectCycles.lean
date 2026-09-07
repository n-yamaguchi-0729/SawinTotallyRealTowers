import ProCGroups.FoxDifferential.Completed.FiniteStage.BoundaryCycleHom

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — semidirect cycles

The principal declarations in this module are:

- `foxAlgebraicStageSemidirectSourceKernelPoint`
  The finite semidirect point \((Dq,1)\) attached to a source-quotient element.
- `foxAlgebraicStageSemidirectKernelWordPoint`
  The finite semidirect point (Dw,1) attached to a word.
- `foxAlgebraicStageSemidirectSourceKernelPoint_left`
  The left coordinate of the finite-stage semidirect point is the specified derivative component.
- `foxAlgebraicStageSemidirectSourceKernelPoint_right`
  The right coordinate of the finite-stage semidirect point is the corresponding quotient component.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite semidirect point \((Dq,1)\) attached to a source-quotient element. -/
def foxAlgebraicStageSemidirectSourceKernelPoint
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    FoxAlgebraicStageSemidirect (X := X) N n :=
  { left := foxAlgebraicStageQuotientDerivativeVector (X := X) N n q,
    right := 1 }

/--
The left coordinate of the finite-stage semidirect point is the specified derivative component.
-/
@[simp]
theorem foxAlgebraicStageSemidirectSourceKernelPoint_left
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    (foxAlgebraicStageSemidirectSourceKernelPoint (X := X) N n q).left =
      foxAlgebraicStageQuotientDerivativeVector (X := X) N n q :=
  rfl

/--
The right coordinate of the finite-stage semidirect point is the corresponding quotient
component.
-/
@[simp]
theorem foxAlgebraicStageSemidirectSourceKernelPoint_right
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    (foxAlgebraicStageSemidirectSourceKernelPoint (X := X) N n q).right = 1 :=
  rfl

/-- The finite semidirect point (Dw,1) attached to a word. -/
def foxAlgebraicStageSemidirectKernelWordPoint (w : FreeGroup X) :
    FoxAlgebraicStageSemidirect (X := X) N n :=
  { left := foxAlgebraicStageDerivativeVector (X := X) N n w,
    right := 1 }

/--
The left coordinate of the finite-stage semidirect point is the specified derivative component.
-/
@[simp]
theorem foxAlgebraicStageSemidirectKernelWordPoint_left (w : FreeGroup X) :
    (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w).left =
      foxAlgebraicStageDerivativeVector (X := X) N n w :=
  rfl

/--
The right coordinate of the finite-stage semidirect point is the corresponding quotient
component.
-/
@[simp]
theorem foxAlgebraicStageSemidirectKernelWordPoint_right (w : FreeGroup X) :
    (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w).right = 1 :=
  rfl

/-- Finite-stage boundary cycles as semidirect points \((v,1)\) with \(\partial v = 0\). -/
def foxAlgebraicStageSemidirectBoundaryCycleSet [Fintype X] :
    Set (FoxAlgebraicStageSemidirect (X := X) N n) :=
  { y | y.right = 1 ∧
      y.left ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n }

omit [DecidableEq X] in
/--
Membership in the finite-stage boundary-cycle object is characterized by the corresponding
boundary-vanishing condition.
-/
@[simp]
theorem mem_foxAlgebraicStageSemidirectBoundaryCycleSet
    (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ) [Fintype X]
    {y : FoxAlgebraicStageSemidirect (X := X) N n} :
    y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n ↔
      y.right = 1 ∧ y.left ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n :=
  Iff.rfl

/-- Semidirect source-kernel derivative points in the finite stage. -/
def foxAlgebraicStageSemidirectSourceKernelDerivativeSet :
    Set (FoxAlgebraicStageSemidirect (X := X) N n) :=
  { y | ∃ q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n,
      foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q = 1 ∧
        foxAlgebraicStageSemidirectSourceKernelPoint (X := X) N n q = y }

/-- This set consists of semidirect kernel-word derivative points at the finite Fox stage. -/
def foxAlgebraicStageSemidirectKernelWordDerivativeSet :
    Set (FoxAlgebraicStageSemidirect (X := X) N n) :=
  { y | ∃ w : FreeGroup X,
      w ∈ N ∧ foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n w = y }

/-- Source-kernel semidirect points and actual kernel-word semidirect points coincide. -/
theorem foxAlgebraicStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet :
    foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n =
      foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N n := by
  ext y
  constructor
  · rintro ⟨q, hq, hy⟩
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
    have hwN : w ∈ N := by
      have hwq : QuotientGroup.mk' N w = 1 := by
        simpa only [foxCommutatorPowerQuotientMapToNormalQuotient_mk] using hq
      exact (QuotientGroup.eq_one_iff (N := N) w).1 hwq
    refine ⟨w, hwN, ?_⟩
    rw [← hy]
    apply FoxAlgebraicStageSemidirect.ext
    · exact (foxAlgebraicStageQuotientDerivativeVector_mk (X := X) N n w).symm
    · simp only [foxAlgebraicStageSemidirectKernelWordPoint,
        foxAlgebraicStageSemidirectSourceKernelPoint,
  QuotientGroup.mk'_apply]
  · rintro ⟨w, hwN, hy⟩
    refine ⟨QuotientGroup.mk'
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w, ?_, ?_⟩
    · rw [foxCommutatorPowerQuotientMapToNormalQuotient_mk]
      exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN
    · rw [← hy]
      apply FoxAlgebraicStageSemidirect.ext
      · exact foxAlgebraicStageQuotientDerivativeVector_mk (X := X) N n w
      · simp only [foxAlgebraicStageSemidirectSourceKernelPoint, QuotientGroup.mk'_apply,
  foxAlgebraicStageSemidirectKernelWordPoint]

/-- Every finite semidirect source-kernel derivative point is a semidirect boundary cycle. -/
theorem foxAlgebraicStageSemidirectSourceKernelDerivativeSet_subset_boundaryCycleSet
    [Fintype X] :
    foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n ⊆
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n := by
  intro y hy
  rcases hy with ⟨q, hq, hy⟩
  rw [← hy]
  constructor
  · simp only [foxAlgebraicStageSemidirectSourceKernelPoint]
  · exact foxAlgebraicStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule
      (X := X) N n ⟨q, hq, rfl⟩

/-- Every finite semidirect kernel-word derivative point is a semidirect boundary cycle. -/
theorem foxAlgebraicStageSemidirectKernelWordDerivativeSet_subset_boundaryCycleSet
    [Fintype X] :
    foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N n ⊆
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n := by
  rw [← foxAlgebraicStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet
    (X := X) N n]
  exact foxAlgebraicStageSemidirectSourceKernelDerivativeSet_subset_boundaryCycleSet
    (X := X) N n

/--
Semidirect finite-stage coverage: every semidirect boundary cycle is represented by a
source-kernel derivative point.
-/
def foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel [Fintype X] : Prop :=
  foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n ⊆
    foxAlgebraicStageSemidirectSourceKernelDerivativeSet (X := X) N n

/-- The semidirect finite-stage coverage target is equivalent to the coordinate coverage target. -/
theorem foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel (X := X) N n ↔
      foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro hcover v hv
    have hy :
        ({ left := v, right := (1 : foxAlgebraicStageTargetQuotient (X := X) N) } :
          FoxAlgebraicStageSemidirect (X := X) N n) ∈
          foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n := by
      exact ⟨rfl, hv⟩
    rcases hcover hy with ⟨q, hq, hqy⟩
    refine ⟨q, hq, ?_⟩
    have hleft := congrArg (fun z : FoxAlgebraicStageSemidirect (X := X) N n => z.left) hqy
    simpa [foxAlgebraicStageSemidirectSourceKernelPoint] using hleft
  · intro hcover y hy
    rcases hy with ⟨hyright, hyleft⟩
    rcases hcover hyleft with ⟨q, hq, hqleft⟩
    refine ⟨q, hq, ?_⟩
    apply FoxAlgebraicStageSemidirect.ext
    · simpa [foxAlgebraicStageSemidirectSourceKernelPoint] using hqleft
    · simpa [foxAlgebraicStageSemidirectSourceKernelPoint] using hyright.symm

/-- Finite-stage semidirect coverage is equivalent to coverage by actual kernel words. -/
theorem foxAlgebraicStageSemidirectBoundaryCyclesCoveredByKernelWords_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n ⊆
        foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N n ↔
      foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  rw [← foxAlgebraicStageSemidirectSourceKernelDerivativeSet_eq_kernelWordDerivativeSet
    (X := X) N n]
  exact foxAlgebraicStageSemidirectBoundaryCyclesCoveredBySourceKernel_iff
    (X := X) (N := N) (n := n)

end

end FoxDifferential
