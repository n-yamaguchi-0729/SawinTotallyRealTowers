/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.LimitMap
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Limit

/-!
# Fox differential: finite stage — prime power — derivative — completed source

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivative`
  The completed source Fox derivative with values in the prime-power finite-stage target limit.
- `primePowerCompletedGroupAlgebraFreeFoxDerivative_projection`
  Projecting the completed source Fox derivative gives its prime-power target-limit coordinate.
- `primePowerCompletedGroupAlgebraFreeFoxDerivative_unique`
  The prime-power completed Fox derivative is uniquely determined by all finite-stage projection
  formulas.
- `primePowerCompletedGroupAlgebraFreeFoxDerivative_fundamental_formula_projection`
  The finite-stage fundamental formula for the completed source Fox derivative after projection to a
  prime-power stage.
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


/-- The completed source Fox derivative with values in the prime-power finite-stage target limit. -/
def primePowerCompletedGroupAlgebraFreeFoxDerivative
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N :=
  (foxAlgebraicStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i).comp
    (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
      (ℓ := ℓ) (X := X) N hfinite)

/-- Projecting the completed source Fox derivative gives its prime-power target-limit coordinate. -/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i z) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite a) z) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivative,
    AddMonoidHom.comp_apply,
    foxAlgebraicStagePrimePowerDerivativeLimitAddHom_apply,
    foxAlgebraicStagePrimePowerDerivativeLimit_projection,
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_projection]

/--
The prime-power completed Fox derivative is uniquely determined by all finite-stage projection
formulas.
-/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X)
    (f : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (hf : ∀ z a,
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (f z) =
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite a) z)) :
    f = primePowerCompletedGroupAlgebraFreeFoxDerivative
      (ℓ := ℓ) (X := X) N hfinite i := by
  apply AddMonoidHom.ext
  intro z
  apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a (f z) =
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraFreeFoxDerivative
          (ℓ := ℓ) (X := X) N hfinite i z)
  rw [hf, primePowerCompletedGroupAlgebraFreeFoxDerivative_projection]

/--
The finite-stage fundamental formula for the completed source Fox derivative after projection to
a prime-power stage.
-/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivative_fundamental_formula_projection
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ a)
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite a) z) -
        algebraMap (ModNCompletedCoeff (ℓ ^ a))
          (foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N (ℓ ^ a)
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
                N hfinite a) z)) =
      ∑ i : X,
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (primePowerCompletedGroupAlgebraFreeFoxDerivative
              (ℓ := ℓ) (X := X) N hfinite i z)) *
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  change
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ a)
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
          (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
            (ℓ := ℓ) (X := X) N hfinite z)) -
        algebraMap (ModNCompletedCoeff (ℓ ^ a))
          (foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N (ℓ ^ a)
            ((foxAlgebraicStagePrimePowerSourceSystem
              (ℓ := ℓ) (X := X) N).projection a
              (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
                (ℓ := ℓ) (X := X) N hfinite z))) =
      ∑ i : X,
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra
            (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerTargetSystem
            (ℓ := ℓ) (X := X) N).projection a
            (foxAlgebraicStagePrimePowerDerivativeLimit
              (ℓ := ℓ) (X := X) N i
              (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
                (ℓ := ℓ) (X := X) N hfinite z))) *
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1)
  exact foxAlgebraicStagePrimePowerDerivativeLimit_fundamental_formula_projection
    (ℓ := ℓ) (X := X) N
    (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
      (ℓ := ℓ) (X := X) N hfinite z) a



end

end FoxDifferential
