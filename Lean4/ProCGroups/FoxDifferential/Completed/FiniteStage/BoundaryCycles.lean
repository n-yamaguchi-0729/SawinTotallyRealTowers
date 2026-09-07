import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Fundamental

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — boundary cycles

The principal declarations in this module are:

- `foxAlgebraicStageBoundaryCycleSubmodule`
  The finite-stage Fox boundary-cycle submodule \(\ker \partial\).
- `foxAlgebraicStageSourceKernelDerivativeSet`
  Quotient-level source-kernel derivatives in the finite stage. These are the finite-stage relation
  cycles coming from the kernel of \(F/[N,N]N^n \to F/N\).
- `mem_foxAlgebraicStageBoundaryCycleSubmodule`
  Membership in the finite-stage boundary-cycle object is characterized by the corresponding
  boundary-vanishing condition.
- `foxAlgebraicStageCoefficient_eq_one_of_mem`
  A word lying in the normal subgroup \(N\) has finite-stage coefficient equal to \(1\) in the
  quotient by \(N\).
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite-stage Fox boundary-cycle submodule \(\ker \partial\). -/
def foxAlgebraicStageBoundaryCycleSubmodule [Fintype X] :
    Submodule (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n) :=
  LinearMap.ker (foxAlgebraicStageFoxBoundary (X := X) N n)

omit [DecidableEq X] in
/--
Membership in the finite-stage boundary-cycle object is characterized by the corresponding
boundary-vanishing condition.
-/
@[simp]
theorem mem_foxAlgebraicStageBoundaryCycleSubmodule [Fintype X]
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {v : foxAlgebraicStageCoordinateVector (X := X) N n} :
    v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n ↔
      foxAlgebraicStageFoxBoundary (X := X) N n v = 0 :=
  Iff.rfl

/--
Quotient-level source-kernel derivatives in the finite stage. These are the finite-stage
relation cycles coming from the kernel of \(F/[N,N]N^n \to F/N\).
-/
def foxAlgebraicStageSourceKernelDerivativeSet :
    Set (foxAlgebraicStageCoordinateVector (X := X) N n) :=
  { v | ∃ q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n,
      foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q = 1 ∧
        foxAlgebraicStageQuotientDerivativeVector (X := X) N n q = v }

/--
Word-level kernel derivatives in the finite stage. This is the algebraic form obtained from
actual relation words w \(\in\) N.
-/
def foxAlgebraicStageKernelWordDerivativeSet :
    Set (foxAlgebraicStageCoordinateVector (X := X) N n) :=
  { v | ∃ w : FreeGroup X,
      w ∈ N ∧ foxAlgebraicStageDerivativeVector (X := X) N n w = v }

omit [DecidableEq X] in
/--
A word lying in the normal subgroup \(N\) has finite-stage coefficient equal to \(1\) in the
quotient by \(N\).
-/
@[simp]
theorem foxAlgebraicStageCoefficient_eq_one_of_mem
    {w : FreeGroup X} (hw : w ∈ N) :
    foxAlgebraicStageCoefficient (X := X) N n w = 1 := by
  rw [foxAlgebraicStageCoefficient_apply]
  have hq : QuotientGroup.mk' N w = 1 :=
    (QuotientGroup.eq_one_iff (N := N) w).2 hw
  rw [hq]
  rfl

omit [DecidableEq X] in
/--
For a kernel element, the finite Fox-stage quotient coefficient evaluates to one after
coefficient change.
-/
@[simp]
theorem foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel
    {q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n}
    (hq : foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q = 1) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n q = 1 := by
  rw [foxAlgebraicStageQuotientCoefficient_apply, hq]
  rfl

/-- Source-kernel derivatives form an additive subgroup of the finite coordinate module. -/
def foxAlgebraicStageSourceKernelDerivativeAddSubgroup :
    AddSubgroup (foxAlgebraicStageCoordinateVector (X := X) N n) where
  carrier := foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n
  zero_mem' := by
    refine ⟨1, ?_, ?_⟩
    · simp only [map_one]
    · exact ScalarCrossedHom.map_one
        (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)
  add_mem' := by
    intro a b ha hb
    rcases ha with ⟨q, hq, hqa⟩
    rcases hb with ⟨r, hr, hrb⟩
    refine ⟨q * r, ?_, ?_⟩
    · rw [map_mul, hq, hr, one_mul]
    · rw [ScalarCrossedHom.map_mul
          (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)]
      rw [foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel (X := X) N n hq]
      simp only [hqa, hrb, one_smul]
  neg_mem' := by
    intro a ha
    rcases ha with ⟨q, hq, hqa⟩
    refine ⟨q⁻¹, ?_, ?_⟩
    · rw [map_inv, hq]
      simp only [inv_one]
    · rw [ScalarCrossedHom.map_inv
          (foxAlgebraicStageQuotientDerivativeVector (X := X) N n)]
      have hcoeff :
          foxAlgebraicStageQuotientCoefficient (X := X) N n q⁻¹ = 1 := by
        apply foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel (X := X) N n
        rw [map_inv, hq]
        simp only [inv_one]
      rw [hcoeff]
      simp only [hqa, one_smul]

/-- The finite-stage source-kernel derivative additive subgroup coerces to its defining carrier. -/
@[simp]
theorem foxAlgebraicStageSourceKernelDerivativeAddSubgroup_coe :
    ((foxAlgebraicStageSourceKernelDerivativeAddSubgroup (X := X) N n :
        AddSubgroup (foxAlgebraicStageCoordinateVector (X := X) N n)) :
          Set (foxAlgebraicStageCoordinateVector (X := X) N n)) =
      foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n :=
  rfl

/--
The quotient-level and word-level descriptions of finite-stage source-kernel derivatives
coincide.
-/
theorem foxAlgebraicStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet :
    foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n =
      foxAlgebraicStageKernelWordDerivativeSet (X := X) N n := by
  ext v
  constructor
  · rintro ⟨q, hq, hv⟩
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
    have hwN : w ∈ N := by
      have hwq : QuotientGroup.mk' N w = 1 := by
        simpa only [foxCommutatorPowerQuotientMapToNormalQuotient_mk] using hq
      exact (QuotientGroup.eq_one_iff (N := N) w).1 hwq
    refine ⟨w, hwN, ?_⟩
    rw [foxAlgebraicStageQuotientDerivativeVector_mk] at hv
    exact hv
  · rintro ⟨w, hwN, hv⟩
    refine ⟨QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w, ?_, ?_⟩
    · rw [foxCommutatorPowerQuotientMapToNormalQuotient_mk]
      exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN
    · rw [foxAlgebraicStageQuotientDerivativeVector_mk]
      exact hv

/-- Every finite-stage source-kernel derivative is a finite Fox boundary cycle. -/
theorem foxAlgebraicStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule
    [Fintype X] :
    foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n ⊆
      (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n :
        Set (foxAlgebraicStageCoordinateVector (X := X) N n)) := by
  intro v hv
  rcases hv with ⟨q, hq, rfl⟩
  change foxAlgebraicStageFoxBoundary (X := X) N n
      (foxAlgebraicStageQuotientDerivativeVector (X := X) N n q) = 0
  rw [foxAlgebraicStageFoxBoundary_quotientDerivativeVector]
  rw [foxAlgebraicStageQuotientCoefficient_eq_one_of_kernel (X := X) N n hq]
  simp only [sub_self]

/--
The finite-stage exactness target: every finite Fox boundary cycle is represented by a
source-kernel derivative in \(F/[N,N]N^n\).
-/
def foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel [Fintype X] : Prop :=
  (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n :
      Set (foxAlgebraicStageCoordinateVector (X := X) N n)) ⊆
    foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n

/-- The finite-stage exactness target is equivalent to the formulation using actual kernel words. -/
theorem foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel_iff_words
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n ↔
      (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n :
          Set (foxAlgebraicStageCoordinateVector (X := X) N n)) ⊆
        foxAlgebraicStageKernelWordDerivativeSet (X := X) N n := by
  rw [foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel,
    foxAlgebraicStageSourceKernelDerivativeSet_eq_kernelWordDerivativeSet]

/--
The finite-stage source-kernel derivative set is equal to \(\ker \partial\) exactly when the
reverse coverage inclusion holds.
-/
theorem foxAlgebraicStageSourceKernelDerivativeSet_eq_boundaryCycleSubmodule_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} [Fintype X] :
    foxAlgebraicStageSourceKernelDerivativeSet (X := X) N n =
        (foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n :
          Set (foxAlgebraicStageCoordinateVector (X := X) N n)) ↔
      foxAlgebraicStageBoundaryCyclesCoveredBySourceKernel (X := X) N n := by
  constructor
  · intro h v hv
    rw [h]
    exact hv
  · intro h
    apply le_antisymm
    · exact foxAlgebraicStageSourceKernelDerivativeSet_subset_boundaryCycleSubmodule (X := X) N n
    · exact h

end

end FoxDifferential
