/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Target

/-!
# Fox differential: finite stage — prime power — derivative — limit

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerDerivativeLimit`
  The inverse-limit Fox derivative obtained by applying the finite-stage derivative at every
  prime-power stage.
- `foxAlgebraicStagePrimePowerDerivativeLimitAddHom`
  The additive-homomorphism version of the prime-power derivative limit.
- `foxAlgebraicStagePrimePowerGroupAlgebraDerivative_transition`
  Naturality of the finite-stage group-algebra Fox derivative along a prime-power transition.
- `foxAlgebraicStagePrimePowerDerivativeLimit_projection`
  Projecting the prime-power derivative limit gives the corresponding finite derivative coordinate.
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


/-- Naturality of the finite-stage group-algebra Fox derivative along a prime-power transition. -/
theorem foxAlgebraicStagePrimePowerGroupAlgebraDerivative_transition
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) (i : X)
    (x : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N
        (primePow_dvd_primePow (ℓ := ℓ) hab)
        (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ b) i x) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        (foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab x) := by
  exact foxAlgebraicStageGroupAlgebraDerivative_powerCoeff_natural
    (X := X) N (primePow_dvd_primePow (ℓ := ℓ) hab) i x

/--
The inverse-limit Fox derivative obtained by applying the finite-stage derivative at every
prime-power stage.
-/
def foxAlgebraicStagePrimePowerDerivativeLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) :
    FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →
      FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N :=
  (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).inverseLimitLift
    (fun a z =>
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z))
    (by
      intro a b hab
      funext z
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ b) i
            ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection b z)) =
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)
      change
        foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N
            (primePow_dvd_primePow (ℓ := ℓ) hab)
            (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ b) i
              (show foxAlgebraicStagePrimePowerSourceGroupAlgebra
                  (ℓ := ℓ) (X := X) N b from
                (foxAlgebraicStagePrimePowerSourceSystem
                  (ℓ := ℓ) (X := X) N).projection b z)) =
          foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
            (show foxAlgebraicStagePrimePowerSourceGroupAlgebra
                (ℓ := ℓ) (X := X) N a from
              (foxAlgebraicStagePrimePowerSourceSystem
                (ℓ := ℓ) (X := X) N).projection a z)
      have hderivative :=
        foxAlgebraicStagePrimePowerGroupAlgebraDerivative_transition
          (ℓ := ℓ) (X := X) N hab i
          (show foxAlgebraicStagePrimePowerSourceGroupAlgebra
              (ℓ := ℓ) (X := X) N b from
            (foxAlgebraicStagePrimePowerSourceSystem
              (ℓ := ℓ) (X := X) N).projection b z)
      exact hderivative.trans
        (congrArg
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i)
          ((foxAlgebraicStagePrimePowerSourceSystem
            (ℓ := ℓ) (X := X) N).projection_compatible z a b hab)))

/--
Projecting the prime-power derivative limit gives the corresponding finite derivative
coordinate.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerDerivativeLimit_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (z : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z) := rfl

/--
The prime-power finite-stage derivative limit is uniquely determined by its projections to all
finite stages.
-/
theorem foxAlgebraicStagePrimePowerDerivativeLimit_unique
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (f : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →
      FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (hf : ∀ z a,
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (f z) =
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)) :
    f = foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i := by
  funext z
  apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a (f z) =
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z)
  rw [hf, foxAlgebraicStagePrimePowerDerivativeLimit_projection]

/--
The finite-stage fundamental formula, expressed after projecting a prime-power derivative limit
to one stage.
-/
theorem foxAlgebraicStagePrimePowerDerivativeLimit_fundamental_formula_projection
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (z : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) (a : ℕ) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ a)
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z) -
        algebraMap (ModNCompletedCoeff (ℓ ^ a))
          (foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N (ℓ ^ a)
            ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)) =
      ∑ i : X,
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z)) *
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rw [foxAlgebraicStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    (X := X) (N := N) (n := ℓ ^ a)
    ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [foxAlgebraicStagePrimePowerDerivativeLimit_projection]

/-- The additive-homomorphism version of the prime-power derivative limit. -/
def foxAlgebraicStagePrimePowerDerivativeLimitAddHom
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) :
    FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →+
      FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N where
  toFun := foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
  map_zero' := by
    apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i 0) =
        (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (0 : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    rw [foxAlgebraicStagePrimePowerDerivativeLimit_projection]
    change foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
          (0 : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N)) = 0
    change foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        (0 : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a) = 0
    exact map_zero _
  map_add' x y := by
    apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i (x + y)) =
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i x)) +
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
            (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i y))
    rw [foxAlgebraicStagePrimePowerDerivativeLimit_projection,
      foxAlgebraicStagePrimePowerDerivativeLimit_projection,
      foxAlgebraicStagePrimePowerDerivativeLimit_projection]
    change foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a (x + y)) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a x) +
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a y)
    change foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from
          (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a x) +
          (show foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a from
            (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a y)) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a x) +
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
        ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a y)
    exact map_add _ _ _

/-- Evaluation formula for the additive-homomorphism version of the derivative limit. -/
@[simp]
theorem foxAlgebraicStagePrimePowerDerivativeLimitAddHom_apply
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (z : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i z =
      foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i z := rfl

/--
Additive maps into the prime-power finite-stage target limit are uniquely determined by the
finite-stage Fox derivative projection formula.
-/
theorem foxAlgebraicStagePrimePowerDerivativeLimitAddHom_unique
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X)
    (f : FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N →+
      FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (hf : ∀ z a,
      (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
          (f z) =
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ a) i
          ((foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a z)) :
    f = foxAlgebraicStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i := by
  apply AddMonoidHom.ext
  intro z
  exact congrFun
    (foxAlgebraicStagePrimePowerDerivativeLimit_unique (ℓ := ℓ) (X := X) N i f hf) z



end

end FoxDifferential
