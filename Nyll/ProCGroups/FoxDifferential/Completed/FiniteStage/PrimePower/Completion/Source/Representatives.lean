/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.LimitMap

/-!
# Fox differential: prime power — completion — source — representatives

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerSourceOf`
  The compatible source-limit family represented by a free-group word.
- `foxAlgebraicStagePrimePowerTargetOf`
  The compatible target-limit family represented by a free-group word.
- `foxAlgebraicStagePrimePowerSourceOf_projection`
  Projecting the source-limit element represented by a word gives the corresponding finite-stage
  source coordinate.
- `foxAlgebraicStagePrimePowerSourceProjection_eq_sourceOf_projection`
  Projecting a group-like free-group algebra element to a source stage agrees with the corresponding
  source-limit projection.
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


/-- The compatible source-limit family represented by a free-group word. -/
def foxAlgebraicStagePrimePowerSourceOf
    (N : Subgroup (FreeGroup X)) (w : FreeGroup X) :
    FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N :=
  ⟨fun a =>
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
            (FreeGroup X ⧸
              foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b))
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b)) w)) =
        MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
          (FreeGroup X ⧸
            foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w)
      exact foxAlgebraicStagePrimePowerSourceTransition_of (ℓ := ℓ) (X := X) N hab w⟩

omit [DecidableEq X] in
/--
Projecting the source-limit element represented by a word gives the corresponding finite-stage
source coordinate.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceOf_projection
    (N : Subgroup (FreeGroup X)) (w : FreeGroup X) (a : ℕ) :
    (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) := rfl

omit [DecidableEq X] in
/--
Projecting a group-like free-group algebra element to a source stage agrees with the
corresponding source-limit projection.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceProjection_eq_sourceOf_projection
    (N : Subgroup (FreeGroup X)) (w : FreeGroup X) (a : ℕ) :
    foxAlgebraicStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X) w) =
      (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w) := by
  rw [foxAlgebraicStagePrimePowerSourceProjection_of,
    foxAlgebraicStagePrimePowerSourceOf_projection]

omit [DecidableEq X] in
/--
The completed-source-to-finite-stage-limit map sends a group-like completed element to the
source-limit element represented by the same word.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w := by
  apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
    (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
      (foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    foxAlgebraicStagePrimePowerSourceOf_projection]
  rfl

omit [DecidableEq X] in
/--
The source-limit bridge sends the completed group-like boundary \([w]-1\) to the corresponding
source-limit boundary.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_sub_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w - 1) =
      foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N w - 1 := by
  rw [map_sub,
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_of,
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_one]

/-- The compatible target-limit family represented by a free-group word. -/
def foxAlgebraicStagePrimePowerTargetOf
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) :
    FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N :=
  ⟨fun a =>
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w),
    by
      intro a b hab
      change foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N w)) =
        MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
          (foxAlgebraicStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N w)
      exact foxAlgebraicStagePrimePowerTargetTransition_of (ℓ := ℓ) (X := X) N hab w⟩

omit [DecidableEq X] in
/--
Projecting the target-limit element represented by a word gives the corresponding finite-stage
target coordinate.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetOf_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection a
        (foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w) := rfl

omit [DecidableEq X] in
/--
The target-limit-to-completed-group-algebra map sends a represented word to the corresponding
group-like element in the completed target group algebra.
-/
@[simp 900]
theorem foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_targetOf
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) i
      (foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w)) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) i
      (primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w))
  rw [foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection,
    foxAlgebraicStagePrimePowerTargetOf_projection,
    modNCompletedGroupAlgebraStageMap_of,
    primePowerCompletedGroupAlgebraProjection_of]
  rfl

omit [DecidableEq X] in
/-- Family-level projection formula for the target-limit element represented by a word. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetOf_toFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    foxAlgebraicStagePrimePowerTargetLimitToFamily (ℓ := ℓ) (X := X) N
        (foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N w) a =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w) := rfl

omit [DecidableEq X] in
/-- The source-limit element represented by the identity word is one. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceOf_one
    (N : Subgroup (FreeGroup X)) :
    foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (1 : FreeGroup X) = 1 := by
  apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (1 : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) =
    (1 : foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a)
  simpa using
    (map_one (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))))

omit [DecidableEq X] in
/-- The source-limit representative of a product is the product of source-limit representatives. -/
theorem foxAlgebraicStagePrimePowerSourceOf_mul
    (N : Subgroup (FreeGroup X)) (u v : FreeGroup X) :
    foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N (u * v) =
      foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N u *
        foxAlgebraicStagePrimePowerSourceOf (ℓ := ℓ) (X := X) N v := by
  apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) (u * v)) =
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) u) *
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
      (QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) v)
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, MonoidAlgebra.of_apply,
  MonoidAlgebra.single_mul_single, mul_one]

omit [DecidableEq X] in
/-- The target-limit element represented by the identity word is one. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetOf_one
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N (1 : FreeGroup X) = 1 := by
  apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (foxAlgebraicStageTargetQuotient (X := X) N)
      (1 : foxAlgebraicStageTargetQuotient (X := X) N) =
    (1 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a)
  simpa using
    (map_one (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (foxAlgebraicStageTargetQuotient (X := X) N)))

omit [DecidableEq X] in
/-- The target-limit representative of a product is the product of target-limit representatives. -/
theorem foxAlgebraicStagePrimePowerTargetOf_mul
    (N : Subgroup (FreeGroup X)) [N.Normal] (u v : FreeGroup X) :
    foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N (u * v) =
      foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N u *
        foxAlgebraicStagePrimePowerTargetOf (ℓ := ℓ) (X := X) N v := by
  apply foxAlgebraicStagePrimePowerTargetLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (foxAlgebraicStageTargetQuotient (X := X) N)
      (QuotientGroup.mk' N (u * v)) =
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u) *
    MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
      (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N v)
  simp only [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, MonoidAlgebra.of_apply,
  MonoidAlgebra.single_mul_single, mul_one]




end

end FoxDifferential
