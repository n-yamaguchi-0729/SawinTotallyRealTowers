import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.Semidirect
import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.Boundary
import ProCGroups.FoxDifferential.Completed.FiniteStage.SemidirectCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — coeff map — boundary cycles

The principal declarations in this module are:

- `foxAlgebraicStageSemidirectCoeffMap_left`
  The left component of finite-stage semidirect coefficient reduction is obtained by reducing each
  coordinate coefficient.
- `foxAlgebraicStageSemidirectCoeffMap_right`
  The right component of finite-stage semidirect coefficient reduction is unchanged.
- `foxAlgebraicStageSemidirectCoeffMap_rfl`
  Coefficient reduction is the identity on finite-stage semidirect targets when the modulus is
  unchanged.
- `foxAlgebraicStageSemidirectCoeffMap_comp`
  Coefficient reductions compose on finite-stage semidirect targets.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
The left component of finite-stage semidirect coefficient reduction is obtained by reducing each
coordinate coefficient.
-/
@[simp]
theorem foxAlgebraicStageSemidirectCoeffMap_left
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (y : FoxAlgebraicStageSemidirect (X := X) N m₀) :
    (foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm y).left =
      fun i : X => foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm (y.left i) :=
  rfl

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- The right component of finite-stage semidirect coefficient reduction is unchanged. -/
@[simp]
theorem foxAlgebraicStageSemidirectCoeffMap_right
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (y : FoxAlgebraicStageSemidirect (X := X) N m₀) :
    (foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm y).right = y.right :=
  rfl

omit [Fact (0 < m₀)] [DecidableEq X] [Fact (0 < n₀)] in
/--
Coefficient reduction is the identity on finite-stage semidirect targets when the modulus is
unchanged.
-/
@[simp]
theorem foxAlgebraicStageSemidirectCoeffMap_rfl
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    foxAlgebraicStageSemidirectCoeffMap
        (X := X) (n₀ := n₀) (m₀ := n₀) N dvd_rfl =
      MonoidHom.id (FoxAlgebraicStageSemidirect (X := X) N n₀) := by
  apply MonoidHom.ext
  intro y
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    change foxAlgebraicStageTargetGroupAlgebraCoeffMap
        (X := X) (n₀ := n₀) (m₀ := n₀) N dvd_rfl (y.left i) = y.left i
    rw [foxAlgebraicStageTargetGroupAlgebraCoeffMap_rfl]
    rfl
  · rfl

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Coefficient reductions compose on finite-stage semidirect targets. -/
@[simp]
theorem foxAlgebraicStageSemidirectCoeffMap_comp
    {k₀ : ℕ}
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hnm : n₀ ∣ m₀) (hmk : m₀ ∣ k₀) :
    (foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm).comp
        (foxAlgebraicStageSemidirectCoeffMap (X := X) N hmk) =
      foxAlgebraicStageSemidirectCoeffMap (X := X) N (dvd_trans hnm hmk) := by
  apply MonoidHom.ext
  intro y
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    change foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hmk (y.left i)) =
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N (dvd_trans hnm hmk) (y.left i)
    exact congrFun
      (congrArg DFunLike.coe
        (foxAlgebraicStageTargetGroupAlgebraCoeffMap_comp (X := X) N hnm hmk))
      (y.left i)
  · rfl

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
Coefficient reduction carries finite semidirect boundary cycles to finite semidirect boundary
cycles.
-/
theorem foxAlgebraicStageSemidirectCoeffMap_mem_boundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    {y : FoxAlgebraicStageSemidirect (X := X) N m₀}
    (hy : y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N m₀) :
    foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm y ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N n₀ := by
  rcases hy with ⟨hyright, hyboundary⟩
  constructor
  · simpa [foxAlgebraicStageSemidirectCoeffMap_right] using hyright
  · simpa [foxAlgebraicStageSemidirectCoeffMap_left] using
      foxAlgebraicStageBoundaryCycleSubmodule_coeffMap_mem
        (X := X) N hnm hyboundary

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
Coefficient reduction sends the finite semidirect kernel-word point at modulus \(m\) to the
corresponding point at modulus \(n\).
-/
theorem foxAlgebraicStageSemidirectCoeffMap_kernelWordPoint
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (w : FreeGroup X) :
    foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm
        (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N m₀ w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N n₀ w := by
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    change foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (foxAlgebraicStageDerivative (X := X) N m₀ i w) =
      foxAlgebraicStageDerivative (X := X) N n₀ i w
    exact foxAlgebraicStageDerivative_coeffMap (X := X) N hnm i w
  · rfl

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
Coefficient reduction sends the finite semidirect kernel-word derivative set at modulus \(m\)
into the corresponding set at modulus \(n\).
-/
theorem foxAlgebraicStageSemidirectCoeffMap_kernelWordDerivativeSet_subset
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    (fun y : FoxAlgebraicStageSemidirect (X := X) N m₀ =>
        foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm y) ''
      foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N m₀ ⊆
        foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N n₀ := by
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  rcases hz with ⟨w, hwN, hzw⟩
  refine ⟨w, hwN, ?_⟩
  rw [← hzw]
  exact (foxAlgebraicStageSemidirectCoeffMap_kernelWordPoint (X := X) N hnm w).symm

end

end FoxDifferential
