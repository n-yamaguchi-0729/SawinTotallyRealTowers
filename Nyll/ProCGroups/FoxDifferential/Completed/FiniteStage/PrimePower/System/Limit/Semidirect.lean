/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Semidirect

/-!
# Fox differential: prime power — system — limit — semidirect

The principal declarations in this module are:

- `FoxAlgebraicStagePrimePowerSemidirectLimit`
  Inverse limit of the prime-power finite Fox semidirect stage system.
- `foxAlgebraicStagePrimePowerSemidirectLimitToFamily`
  Forget a semidirect inverse-limit element to its compatible family of finite stages.
- `foxAlgebraicStagePrimePowerSemidirectLimitToFamily_injective`
  The family map out of the semidirect inverse limit is injective.
- `foxAlgebraicStagePrimePowerSemidirectLimitProjection_apply`
  The prime-power semidirect inverse-limit projection returns the coordinate at the selected
  exponent.
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

/-- Inverse limit of the prime-power finite Fox semidirect stage system. -/
abbrev FoxAlgebraicStagePrimePowerSemidirectLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] : Type u :=
  (foxAlgebraicStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N).inverseLimit

/-- Forget a semidirect inverse-limit element to its compatible family of finite stages. -/
def foxAlgebraicStagePrimePowerSemidirectLimitToFamily
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N →
      ((a : ℕ) → FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a)) :=
  fun z a => z.1 a

omit [Fact (0 < ℓ)] [DecidableEq X] in
/-- The family map out of the semidirect inverse limit is injective. -/
theorem foxAlgebraicStagePrimePowerSemidirectLimitToFamily_injective
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Function.Injective
      (foxAlgebraicStagePrimePowerSemidirectLimitToFamily (ℓ := ℓ) (X := X) N) := by
  intro x y h
  apply Subtype.ext
  funext a
  exact congrFun h a

/-- The \(a\)-th finite-stage projection from the semidirect prime-power inverse limit. -/
def foxAlgebraicStagePrimePowerSemidirectLimitProjection
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N →
      FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a) :=
  (foxAlgebraicStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N).projection a

omit [Fact (0 < ℓ)] [DecidableEq X] in
/--
The prime-power semidirect inverse-limit projection returns the coordinate at the selected exponent.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerSemidirectLimitProjection_apply
    (N : Subgroup (FreeGroup X)) [N.Normal]
    (z : FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N) (a : ℕ) :
    foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z = z.1 a :=
  rfl

omit [Fact (0 < ℓ)] [DecidableEq X] in
/--
The finite-stage projections of a semidirect limit element are compatible with the prime-power
transition maps.
-/
theorem foxAlgebraicStagePrimePowerSemidirectLimitProjection_transition
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b)
    (z : FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
        (foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N b z) =
      foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z := by
  exact (foxAlgebraicStagePrimePowerSemidirectSystem
    (ℓ := ℓ) (X := X) N).projection_compatible z a b hab

/-- Boundary-cycle condition for a prime-power semidirect limit element, read stagewise. -/
def foxAlgebraicStagePrimePowerSemidirectLimitBoundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    Set (FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N) :=
  { z | ∀ a : ℕ,
      foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z ∈
        foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) }

omit [DecidableEq X] in
/--
Membership in the finite-stage boundary-cycle object is characterized by the corresponding
boundary-vanishing condition.
-/
@[simp]
theorem mem_foxAlgebraicStagePrimePowerSemidirectLimitBoundaryCycleSet
    {ℓ : ℕ} [Fact (0 < ℓ)] [Fintype X]
    {N : Subgroup (FreeGroup X)} [N.Normal]
    {z : FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N} :
    z ∈ foxAlgebraicStagePrimePowerSemidirectLimitBoundaryCycleSet (ℓ := ℓ) (X := X) N ↔
      ∀ a : ℕ,
        foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a z ∈
          foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) :=
  Iff.rfl

/--
The compatible semidirect limit point represented by the finite kernel-word points for one
free-group word.
-/
def foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) :
    FoxAlgebraicStagePrimePowerSemidirectLimit (ℓ := ℓ) (X := X) N :=
  ⟨fun a => foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w,
    by
      intro a b hab
      exact foxAlgebraicStagePrimePowerSemidirectTransition_kernelWordPoint
        (ℓ := ℓ) (X := X) N hab w⟩

omit [Fact (0 < ℓ)] in
/--
The kernel-word point in the semidirect inverse limit projects to the corresponding finite
semidirect stage.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit_projection
    (N : Subgroup (FreeGroup X)) [N.Normal] (w : FreeGroup X) (a : ℕ) :
    foxAlgebraicStagePrimePowerSemidirectLimitProjection (ℓ := ℓ) (X := X) N a
        (foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit
          (ℓ := ℓ) (X := X) N w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w :=
  rfl

omit [Fact (0 < ℓ)] in
/--
If w is a relation word, its compatible prime-power semidirect point is a stagewise boundary
cycle.
-/
theorem foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit_mem_boundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {w : FreeGroup X} (hw : w ∈ N) :
    foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit (ℓ := ℓ) (X := X) N w ∈
      foxAlgebraicStagePrimePowerSemidirectLimitBoundaryCycleSet (ℓ := ℓ) (X := X) N := by
  intro a
  have hstage :
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w ∈
        foxAlgebraicStageSemidirectKernelWordDerivativeSet (X := X) N (ℓ ^ a) := by
    exact ⟨w, hw, rfl⟩
  rw [foxAlgebraicStagePrimePowerSemidirectKernelWordPointLimit_projection]
  exact foxAlgebraicStageSemidirectKernelWordDerivativeSet_subset_boundaryCycleSet
    (X := X) N (ℓ ^ a) hstage

end

end FoxDifferential
