/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.SpecialValues

/-!
# Fox differential: prime power — derivative — on group — projection

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivative_generator_projection`
  The generator-value projection formula for the completed source Fox derivative.
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


omit [Fact (0 < ℓ)] in
/-- The generator-value projection formula for the completed source Fox derivative. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_generator_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i j : X) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
            (FreeGroup.of j))) =
      ((Pi.single j (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
        X → foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection]
  change foxAlgebraicStageDerivativeVector (X := X) N (ℓ ^ a) (FreeGroup.of j) i =
    ((Pi.single j (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
      X → foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i
  rw [foxAlgebraicStageDerivativeVector_of]




end

end FoxDifferential
