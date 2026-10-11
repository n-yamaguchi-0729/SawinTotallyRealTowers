/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.TargetQuotient.StageMap
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Fundamental
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.Mul

/-!
# Fox differential: completed — differential module — target quotient — fundamental

The principal declarations in this module are:

- `ppCompletedGAFoxDerivToTarget_of_fundFormula_map`
  The completed Fox derivative satisfies the fundamental formula after passage to the target
  quotient.
- `ppCompletedGAFoxDerivToTarget_of_mul_product_map`
  The completed Fox derivative of a product is computed by the crossed product rule after passage to
  the target quotient.
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
The completed Fox derivative satisfies the fundamental formula after passage to the target
quotient.
-/
theorem ppCompletedGAFoxDerivToTarget_of_fundFormula_map
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) - 1 =
      ∑ i : X,
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) *
          (primePowerCompletedGroupAlgebraMap
            (ℓ := ℓ) (G := FreeGroup X)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
              (FreeGroup.of i)) - 1) := by
  rw [primePowerCompletedGroupAlgebraMap_targetQuotient_of]
  simp_rw [primePowerCompletedGroupAlgebraMap_targetQuotient_of]
  exact ppCompletedGAFoxDerivToTarget_of_fundFormula
    (ℓ := ℓ) (X := X) N hfinite w

/--
The completed Fox derivative of a product is computed by the crossed product rule after passage
to the target quotient.
-/
theorem ppCompletedGAFoxDerivToTarget_of_mul_product_map
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (u v : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u *
          primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) +
        primePowerCompletedGroupAlgebraMap
          (ℓ := ℓ) (G := FreeGroup X)
          (H := foxAlgebraicStageTargetQuotient (X := X) N)
          (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) u) *
          primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) v) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_mul_product,
    primePowerCompletedGroupAlgebraMap_targetQuotient_of]


end

end FoxDifferential
