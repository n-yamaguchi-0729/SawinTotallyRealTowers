/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Basic

/-!
# Fox differential: finite stage — prime power — system — semidirect

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerSemidirectTransition`
  Coefficient reduction between prime-power finite Fox semidirect stages.
- `foxAlgebraicStagePrimePowerSemidirectSystem`
  The inverse system of finite Fox semidirect stages over prime-power coefficients.
- `foxAlgebraicStagePrimePowerSemidirectTransition_left`
  The left coordinate of the finite-stage semidirect point is the specified derivative component.
- `foxAlgebraicStagePrimePowerSemidirectTransition_right`
  The right coordinate of the finite-stage semidirect point is the corresponding quotient component.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [hℓ : Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Every prime-power modulus \(\ell^a\) used in the finite Fox stage is positive. -/
instance foxAlgebraicStagePrimePowerFactPos (a : ℕ) : Fact (0 < ℓ ^ a) :=
  ⟨primePower_pos ℓ a⟩

/-- Coefficient reduction between prime-power finite Fox semidirect stages. -/
def foxAlgebraicStagePrimePowerSemidirectTransition
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) :
    FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ b) →*
      FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a) := by
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  haveI : Fact (0 < ℓ ^ b) := ⟨primePower_pos ℓ b⟩
  exact foxAlgebraicStageSemidirectCoeffMap (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] hℓ in
/--
The left coordinate of the finite-stage semidirect point is the specified derivative component.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerSemidirectTransition_left
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b)
    (y : FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ b)) :
    (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab y).left =
      fun i : X =>
        foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab (y.left i) := by
  rfl

omit [DecidableEq X] hℓ in
/--
The right coordinate of the finite-stage semidirect point is the corresponding quotient
component.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerSemidirectTransition_right
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b)
    (y : FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ b)) :
    (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab y).right =
      y.right := by
  rfl

omit [DecidableEq X] hℓ in
/-- The prime-power semidirect transition from a stage to itself is the identity. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSemidirectTransition_id
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    foxAlgebraicStagePrimePowerSemidirectTransition
        (ℓ := ℓ) (X := X) N (le_rfl : a ≤ a) =
      MonoidHom.id (FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a)) := by
  change foxAlgebraicStageSemidirectCoeffMap
      (X := X) (n₀ := ℓ ^ a) (m₀ := ℓ ^ a) N dvd_rfl =
    MonoidHom.id (FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a))
  exact foxAlgebraicStageSemidirectCoeffMap_rfl (X := X) N

omit [DecidableEq X] hℓ in
/-- Prime-power semidirect transitions compose along the stage order. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSemidirectTransition_comp
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab).comp
        (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hbc) =
      foxAlgebraicStagePrimePowerSemidirectTransition
        (ℓ := ℓ) (X := X) N (hab.trans hbc) := by
  change (foxAlgebraicStageSemidirectCoeffMap (X := X) N
        (primePow_dvd_primePow (ℓ := ℓ) hab)).comp
      (foxAlgebraicStageSemidirectCoeffMap (X := X) N
        (primePow_dvd_primePow (ℓ := ℓ) hbc)) =
    foxAlgebraicStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) (hab.trans hbc))
  simp only [foxAlgebraicStageSemidirectCoeffMap_comp]

/-- The inverse system of finite Fox semidirect stages over prime-power coefficients. -/
def foxAlgebraicStagePrimePowerSemidirectSystem
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    InverseSystem (I := ℕ) where
  X := fun a => FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a)
  topologicalSpace := fun _ => ⊥
  map := fun {a b} hab =>
    foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
  continuous_map := by
    intro a b hab
    let : TopologicalSpace (FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a)) := ⊥
    let : TopologicalSpace (FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ b)) := ⊥
    let : DiscreteTopology (FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ b)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro a
    funext y
    exact congrArg (fun f : FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a) →*
        FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a) => f y)
      (foxAlgebraicStagePrimePowerSemidirectTransition_id (ℓ := ℓ) (X := X) N a)
  map_comp := by
    intro a b c hab hbc
    funext y
    exact congrArg (fun f : FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ c) →*
        FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ a) => f y)
      (foxAlgebraicStagePrimePowerSemidirectTransition_comp
        (ℓ := ℓ) (X := X) N hab hbc)

/-- The finite-stage semidirect system carries its group structure. -/
instance instGroupFoxAlgebraicStagePrimePowerSemidirectSystemX
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    Group ((foxAlgebraicStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N).X a) := by
  dsimp [foxAlgebraicStagePrimePowerSemidirectSystem]
  haveI : Fact (0 < ℓ ^ a) := ⟨primePower_pos ℓ a⟩
  infer_instance

/-- The finite-stage semidirect system is a compatible group system. -/
instance instIsGroupSystemFoxAlgebraicStagePrimePowerSemidirectSystem
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    IsGroupSystem (foxAlgebraicStagePrimePowerSemidirectSystem (ℓ := ℓ) (X := X) N) where
  map_one := by
    intro a b hab
    exact map_one (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab)
  map_mul := by
    intro a b hab x y
    exact map_mul (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab) x y
  map_inv := by
    intro a b hab x
    exact map_inv (foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab) x

omit hℓ in
/-- Prime-power semidirect transitions carry finite lifts to finite lifts. -/
theorem foxAlgebraicStagePrimePowerSemidirectTransition_lift
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
        (foxAlgebraicStageLift (X := X) N (ℓ ^ b) w) =
      foxAlgebraicStageLift (X := X) N (ℓ ^ a) w := by
  change foxAlgebraicStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) hab)
        (foxAlgebraicStageLift (X := X) N (ℓ ^ b) w) =
    foxAlgebraicStageLift (X := X) N (ℓ ^ a) w
  exact foxAlgebraicStageSemidirectCoeffMap_lift (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit hℓ in
/-- Prime-power semidirect transitions carry kernel-word points to kernel-word points. -/
theorem foxAlgebraicStagePrimePowerSemidirectTransition_kernelWordPoint
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab
        (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ b) w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w := by
  change foxAlgebraicStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) hab)
        (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ b) w) =
    foxAlgebraicStageSemidirectKernelWordPoint (X := X) N (ℓ ^ a) w
  exact foxAlgebraicStageSemidirectCoeffMap_kernelWordPoint (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [DecidableEq X] hℓ in
/-- Prime-power semidirect transitions preserve finite boundary-cycle points. -/
theorem foxAlgebraicStagePrimePowerSemidirectTransition_mem_boundaryCycleSet
    [Fintype X]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    {a b : ℕ} (hab : a ≤ b)
    {y : FoxAlgebraicStageSemidirect (X := X) N (ℓ ^ b)}
    (hy : y ∈ foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ b)) :
    foxAlgebraicStagePrimePowerSemidirectTransition (ℓ := ℓ) (X := X) N hab y ∈
      foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a) := by
  change foxAlgebraicStageSemidirectCoeffMap (X := X) N
      (primePow_dvd_primePow (ℓ := ℓ) hab) y ∈
    foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) N (ℓ ^ a)
  exact foxAlgebraicStageSemidirectCoeffMap_mem_boundaryCycleSet (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) hy

end

end FoxDifferential
