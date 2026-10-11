/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike

/-!
# Fox differential: prime power — derivative — source — special values

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_one`
  The completed-target Fox derivative sends the unit of the completed source group algebra to zero.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_sub_one`
  Subtracting the unit from a group-like source element does not change its completed-target Fox
  derivative.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_sub_one`
  Subtracting the unit from a group-like source element does not change its completed-target Fox
  derivative vector.
- `foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_toFamily`
  Family-level projection formula for the derivative limit of a group-like source element.
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
/--
The completed-target Fox derivative sends the unit of the completed source group algebra to
zero.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 0 := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro j
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
      (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
      (0 : PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N))
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection,
    primePowerCompletedGroupAlgebraProjection_zero,
    primePowerCompletedGroupAlgebraProjection_one]
  change
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxAlgebraicStageGroupAlgebraDerivative
          (X := X) N (ℓ ^ j.1) i
          (1 : foxAlgebraicStagePrimePowerSourceGroupAlgebra
            (ℓ := ℓ) (X := X) N j.1)) = 0
  rw [foxAlgebraicStageGroupAlgebraDerivative_one]
  exact RingHom.map_zero
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) j.2)

omit [Fact (0 < ℓ)] in
/--
Subtracting the unit from a group-like source element does not change its completed-target Fox
derivative.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_sub_one
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
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w - 1) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite i
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) := by
  rw [map_sub, primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_one, sub_zero]

omit [Fact (0 < ℓ)] in
/--
Subtracting the unit from a group-like source element does not change its completed-target Fox
derivative vector.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_sub_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w - 1) =
      primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) := by
  funext i
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeVectorToCompletedTarget_apply,
    primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_sub_one]

omit [Fact (0 < ℓ)] in
/-- Family-level projection formula for the derivative limit of a group-like source element. -/
@[simp]
theorem foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_toFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) (w : FreeGroup X) (a : ℕ) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N
        (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
          (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)) a =
      foxAlgebraicStageDerivative (X := X) N (ℓ ^ a) i w := by
  exact foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_projection (ℓ := ℓ) (X := X) N i w a

omit [Fact (0 < ℓ)] in
/-- Product rule for the prime-power derivative limit on group-like source elements. -/
theorem foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_mul
    (N : Subgroup (FreeGroup X)) [N.Normal] (i : X) (u v : FreeGroup X) :
    foxAlgebraicStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i
        (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (u * v)) =
      foxAlgebraicStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i
          (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N u) +
        foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N u *
          foxAlgebraicStagePrimePowerDerivativeLimitAddHom (ℓ := ℓ) (X := X) N i
            (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N v) := by
  apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  simp only [foxAlgebraicStagePrimePowerDerivativeLimitAddHom_apply,
  foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_toFamily, foxAlgebraicStageDerivative_mul,
      QuotientGroup.mk'_apply,
  MonoidAlgebra.of_apply, foxAlgebraicStagePrimePowerTargetLimitToFamily_add,
  foxAlgebraicStagePrimePowerTargetLimitToFamily_mul, Pi.add_apply, Pi.mul_apply,
  foxAlgebraicStagePrimePowerTargetOf_toFamily]

omit [Fact (0 < ℓ)] in
/-- The generator-value projection formula for the prime-power derivative limit. -/
@[simp]
theorem foxAlgebraicStagePrimePowerDerivativeLimit_generator_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (i j : X) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerDerivativeLimit (ℓ := ℓ) (X := X) N i
          (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (FreeGroup.of j))) =
      ((Pi.single j (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
        X → foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i := by
  rw [foxAlgebraicStagePrimePowerDerivativeLimit_sourceOf_projection]
  change foxAlgebraicStageDerivativeVector (X := X) N (ℓ ^ a) (FreeGroup.of j) i =
    ((Pi.single j (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a))) :
      X → foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a)) i
  rw [foxAlgebraicStageDerivativeVector_of]

omit [Fact (0 < ℓ)] in
/-- The generator-value projection formula for the completed-target Fox derivative. -/
@[simp 900]
theorem ppCompletedGAFoxDerivToTarget_generator_proj
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i j : X)
    (k : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) k
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X)
            (FreeGroup.of j))) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ k.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) k.2
        (((Pi.single j
          (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1))) :
            X → foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1)) i) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_projection]
  congr 1
  change foxAlgebraicStageDerivativeVector (X := X) N (ℓ ^ k.1) (FreeGroup.of j) i =
    ((Pi.single j (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1))) :
      X → foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ k.1)) i
  rw [foxAlgebraicStageDerivativeVector_of]



end

end FoxDifferential
