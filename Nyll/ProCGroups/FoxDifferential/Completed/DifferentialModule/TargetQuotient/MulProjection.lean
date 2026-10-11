/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.TargetQuotient.Fundamental

/-!
# Fox differential: completed — differential module — target quotient — mul projection

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_mul_projection`
  The finite-stage projection of the prime-power completed target derivative satisfies the Fox
  product rule.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]

/--
The finite-stage projection of the prime-power completed target derivative satisfies the Fox
product rule.
-/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_mul_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (x y : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i (x * y)) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := FreeGroup X)
          (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
            (ℓ := ℓ) (X := X) N hfinite j.1)
          (primePowerCompletedGroupAlgebraAugmentation
            (ℓ := ℓ) (G := FreeGroup X) y) •
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i x) +
      primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraMap
            (ℓ := ℓ) (G := FreeGroup X)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) x) *
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i y) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection,
    primePowerCompletedGroupAlgebraProjection_mul]
  change
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ j.1) i
          ((show foxAlgebraicStageSourceGroupAlgebra (X := X) N (ℓ ^ j.1) from
              primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
                (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
                  (ℓ := ℓ) (X := X) N hfinite j.1) x) *
            (show foxAlgebraicStageSourceGroupAlgebra (X := X) N (ℓ ^ j.1) from
              primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
                (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
                  (ℓ := ℓ) (X := X) N hfinite j.1) y))) =
      _
  rw [foxAlgebraicStageGroupAlgebraDerivative_mul]
  rw [map_add, map_mul]
  rw [show
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
          (foxAlgebraicStageTargetQuotient (X := X) N) j.2
          (foxCommutatorPowerGroupAlgebraMap
            (F := FreeGroup X) N (ℓ ^ j.1)
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1) x)) =
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraMap
            (ℓ := ℓ) (G := FreeGroup X)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) x) by
      rw [primePowerCompletedGAProj_map_targetQuotient_eq_freeDerivativeSource]]
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection]
  rw [foxCommutatorPowerSourceGroupAlgebraAugmentation_projection_eq_completed
    (ℓ := ℓ) (X := X) N hfinite y j.1]
  rw [Algebra.smul_def, map_mul, modNCompletedGroupAlgebraStageMap_algebraMap,
    ← Algebra.smul_def]


end

end FoxDifferential
