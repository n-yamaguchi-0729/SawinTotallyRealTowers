/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedTarget

/-!
# Fox differential: finite stage — prime power — derivative — vector

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget`
  The vector of all completed-target Fox derivatives, indexed by free generators.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply`
  Evaluation of the completed-target derivative vector at a coordinate.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The vector of all completed-target Fox derivatives, indexed by free generators. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      (X → PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)) where
  toFun z i :=
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite i z
  map_zero' := by
    funext i
    exact map_zero
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i)
  map_add' z z' := by
    funext i
    exact map_add
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i) z z'

/-- Evaluation of the completed-target derivative vector at a coordinate. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (i : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite z i =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i z := rfl



end

end FoxDifferential
