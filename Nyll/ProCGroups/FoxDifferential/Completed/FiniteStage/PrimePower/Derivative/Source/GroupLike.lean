/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Representatives
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedSource
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedTarget
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Limit
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Vector

/-!
# Fox differential: prime power — derivative — source — group like

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivative_of`
  The completed source Fox derivative on a group-like element agrees with the prime-power
  finite-stage derivative limit of the same word.
- `foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_projection`
  Projecting the derivative limit of a group-like finite-stage source element gives the
  corresponding derivative coordinate.
- `foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_fundamental_formula`
  Fundamental formula for a group-like finite-stage source element at one prime-power stage.
- `primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection`
  Projecting the completed source Fox derivative evaluated on a group-like element gives the
  corresponding finite-stage derivative value.
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


/--
The completed source Fox derivative on a group-like element agrees with the prime-power
finite-stage derivative limit of the same word.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivative
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      foxAlgebraicStagePrimePowerDerivativeLimit
        (ℓ := ℓ) (X := X) N i
        (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w) := by
  simp only [primePowerCompletedGroupAlgebraFreeFoxDerivative, AddMonoidHom.coe_comp,
      Function.comp_apply,
  primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_of,
  foxAlgebraicStagePrimePowerDerivativeLimitAddHom_apply]

/--
Projecting the derivative limit of a group-like finite-stage source element gives the
corresponding derivative coordinate.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) (w : FreeGroup X) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
          (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)) =
      foxAlgebraicStageDerivative (X := X) N (ℓ ^ a) i w := by
  rw [foxAlgebraicStagePrimePowerDerivativeLimit_projection,
    foxAlgebraicStagePrimePowerSourceOf_projection,
    foxAlgebraicStageGroupAlgebraDerivative_of]

/-- Fundamental formula for a group-like finite-stage source element at one prime-power stage. -/
theorem foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_fundamental_formula
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1 =
      ∑ i : X,
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
              (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w))) *
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rw [foxAlgebraicStageDerivative_fundamental_formula (X := X) (N := N) (n := ℓ ^ a) w]
  apply Finset.sum_congr rfl
  intro i hi
  rw [foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_projection]

/--
Projecting the completed source Fox derivative evaluated on a group-like element gives the
corresponding finite-stage derivative value.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)) =
      foxAlgebraicStageDerivative (X := X) N (ℓ ^ a) i w := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative_of,
    foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_projection]

/--
The completed-target derivative of a group-like source element is the image of the prime-power
derivative limit in the completed target group algebra.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (foxAlgebraicStagePrimePowerDerivativeLimit
          (ℓ := ℓ) (X := X) N i
          (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget,
    AddMonoidHom.comp_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_of]

/--
Projecting the completed-target derivative evaluated on a group-like source element gives the
corresponding finite-stage derivative value.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (w : FreeGroup X)
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxAlgebraicStageDerivative (X := X) N (ℓ ^ j.1) i w) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget,
    AddMonoidHom.comp_apply,
    foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_of_projection]



end

end FoxDifferential
