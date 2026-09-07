import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.Target
import ProCGroups.FoxDifferential.Completed.FiniteStage.BoundaryCycles

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — coeff map — boundary

The principal declarations in this module are:

- `foxAlgebraicStageFoxBoundary_coeffMap`
  Coefficient reduction commutes with the finite-stage Fox boundary map.
- `foxAlgebraicStageBoundaryCycleSubmodule_coeffMap_mem`
  A vector is a boundary cycle after coefficient reduction whenever it was one before reduction.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
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
/-- Coefficient reduction commutes with the finite-stage Fox boundary map. -/
theorem foxAlgebraicStageFoxBoundary_coeffMap
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (v : foxAlgebraicStageCoordinateVector (X := X) N m₀) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (foxAlgebraicStageFoxBoundary (X := X) N m₀ v) =
      foxAlgebraicStageFoxBoundary (X := X) N n₀
        (fun i : X =>
          foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i)) := by
  rw [foxAlgebraicStageFoxBoundary_apply, foxAlgebraicStageFoxBoundary_apply]
  simp only [QuotientGroup.mk'_apply, MonoidAlgebra.of_apply, map_sum, map_mul, map_sub,
  foxAlgebraicStageTargetGroupAlgebraCoeffMap_single_apply, map_one]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
A vector is a boundary cycle after coefficient reduction whenever it was one before reduction.
-/
theorem foxAlgebraicStageBoundaryCycleSubmodule_coeffMap_mem
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    {v : foxAlgebraicStageCoordinateVector (X := X) N m₀}
    (hv : v ∈ foxAlgebraicStageBoundaryCycleSubmodule (X := X) N m₀) :
    (fun i : X =>
        foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i)) ∈
      foxAlgebraicStageBoundaryCycleSubmodule (X := X) N n₀ := by
  rw [mem_foxAlgebraicStageBoundaryCycleSubmodule]
  rw [← foxAlgebraicStageFoxBoundary_coeffMap (X := X) N hnm v]
  rw [mem_foxAlgebraicStageBoundaryCycleSubmodule] at hv
  rw [hv]
  exact map_zero _

end

end FoxDifferential
