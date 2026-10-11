/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.BoundaryCycles

/-!
# Fox differential: finite stage — prime power — system — basic

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerSourceGroupAlgebra`
  Source group algebra at the \(\ell^a\) finite Fox stage.
- `foxAlgebraicStagePrimePowerTargetGroupAlgebra`
  Target group algebra at the \(\ell^a\) finite Fox stage.
- `foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition_of`
  Coefficient reduction sends a group-like free-group element to the same group-like element at the
  lower prime-power stage.
- `foxAlgebraicStagePrimePowerSourceProjection_of`
  Evaluation of the source projection on a group-like free-group algebra element.
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
/-- Source group algebra at the \(\ell^a\) finite Fox stage. -/
abbrev foxAlgebraicStagePrimePowerSourceGroupAlgebra
    (N : Subgroup (FreeGroup X)) (a : ℕ) : Type u :=
  MonoidAlgebra (ModNCompletedCoeff (ℓ ^ a))
    (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))

omit [Fact (0 < ℓ)] in
/-- Target group algebra at the \(\ell^a\) finite Fox stage. -/
abbrev foxAlgebraicStagePrimePowerTargetGroupAlgebra
    (N : Subgroup (FreeGroup X)) (a : ℕ) : Type u :=
  foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ a)

omit [Fact (0 < ℓ)] in
/-- The free-group algebra with coefficients modulo \(\ell^a\). -/
abbrev foxAlgebraicStagePrimePowerFreeGroupAlgebra (a : ℕ) : Type u :=
  MonoidAlgebra (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X)

omit [Fact (0 < ℓ)] in
/-- Coefficient reduction on free-group algebras between prime-power stages. -/
def foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition
    {a b : ℕ} (hab : a ≤ b) :
    foxAlgebraicStagePrimePowerFreeGroupAlgebra (ℓ := ℓ) (X := X) b →+*
      foxAlgebraicStagePrimePowerFreeGroupAlgebra (ℓ := ℓ) (X := X) a :=
  modNCompletedGroupRingCoeffMap (n := ℓ ^ a) (m := ℓ ^ b)
    (FreeGroup X) (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] [Fact (0 < ℓ)] in
/--
Coefficient reduction sends a group-like free-group element to the same group-like element at
the lower prime-power stage.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition_of
    {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition (ℓ := ℓ) (X := X) hab
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b)) (FreeGroup X) w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X) w := by
  exact modNCompletedGroupRingCoeffMap_of (n := ℓ ^ a) (m := ℓ ^ b)
    (H := FreeGroup X) (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [Fact (0 < ℓ)] in
/--
The projection from the free-group algebra to the finite Fox source quotient at a prime-power
stage.
-/
def foxAlgebraicStagePrimePowerSourceProjection
    (N : Subgroup (FreeGroup X)) (a : ℕ) :
    foxAlgebraicStagePrimePowerFreeGroupAlgebra (ℓ := ℓ) (X := X) a →+*
      foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff (ℓ ^ a))
    (QuotientGroup.mk'
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation of the source projection on a group-like free-group algebra element. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceProjection_of
    (N : Subgroup (FreeGroup X)) (a : ℕ) (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a)) (FreeGroup X) w) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) := by
  change
    MonoidAlgebra.mapDomain
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
        (MonoidAlgebra.single w 1) =
      MonoidAlgebra.single
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) 1
  exact MonoidAlgebra.mapDomain_single

omit [Fact (0 < ℓ)] in
/-- Transition map for the finite Fox source quotient group algebras along prime-power stages. -/
def foxAlgebraicStagePrimePowerSourceTransition
    (N : Subgroup (FreeGroup X)) {a b : ℕ} (hab : a ≤ b) :
    foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b →+*
      foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a :=
  foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation of a source transition map on a group-like quotient element. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceTransition_of
    (N : Subgroup (FreeGroup X)) {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
          (FreeGroup X ⧸
            foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b))
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b)) w)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (FreeGroup X ⧸
          foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)) w) := by
  exact foxAlgebraicStagePowerSourceGroupAlgebraMap_of (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- The source transition map from a stage to itself is the identity. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceTransition_id
    (N : Subgroup (FreeGroup X)) (a : ℕ) :
    foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N
        (le_rfl : a ≤ a) =
      RingHom.id _ := by
  simp only [foxAlgebraicStagePrimePowerSourceTransition,
      foxAlgebraicStagePowerSourceGroupAlgebraMap_rfl]

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Source transition maps compose along the order on prime-power stages. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceTransition_comp
    (N : Subgroup (FreeGroup X)) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab).comp
        (foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hbc) =
      foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N (hab.trans hbc) := by
  simp only [foxAlgebraicStagePrimePowerSourceTransition,
      foxAlgebraicStagePowerSourceGroupAlgebraMap_comp]

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Source projection commutes with coefficient reduction and the source transition map. -/
theorem foxAlgebraicStagePrimePowerSourceProjection_transition
    (N : Subgroup (FreeGroup X)) {a b : ℕ} (hab : a ≤ b) :
    (foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab).comp
        (foxAlgebraicStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N b) =
      (foxAlgebraicStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a).comp
        (foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition (ℓ := ℓ) (X := X) hab) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab).comp
          (foxAlgebraicStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N b)) x =
        ((foxAlgebraicStagePrimePowerSourceProjection (ℓ := ℓ) (X := X) N a).comp
          (foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition (ℓ := ℓ) (X := X) hab)) x)
    x ?_ ?_ ?_
  · intro w
    rw [RingHom.comp_apply, RingHom.comp_apply,
      foxAlgebraicStagePrimePowerSourceProjection_of,
      foxAlgebraicStagePrimePowerSourceTransition_of,
      foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition_of,
      foxAlgebraicStagePrimePowerSourceProjection_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro r x hx
    rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [foxAlgebraicStagePrimePowerSourceTransition,
        foxAlgebraicStagePowerSourceGroupAlgebraMap,
  foxAlgebraicStageSameSourceGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap,
      AlgHom.toRingHom_eq_coe,
  foxAlgebraicStagePrimePowerSourceProjection, map_intCast,
      foxAlgebraicStagePrimePowerFreeGroupAlgebraTransition,
  RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
      QuotientGroup.coe_mk']

omit [Fact (0 < ℓ)] in
/-- Transition map for the finite Fox target group algebras along prime-power stages. -/
def foxAlgebraicStagePrimePowerTargetTransition
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) :
    foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b →+*
      foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a :=
  foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Evaluation of a target transition map on a group-like target quotient element. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetTransition_of
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b : ℕ} (hab : a ≤ b) (w : FreeGroup X) :
    foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
          (foxAlgebraicStageTargetQuotient (X := X) N)
          (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ a))
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (QuotientGroup.mk' N w) := by
  exact foxAlgebraicStageTargetGroupAlgebraCoeffMap_of (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab) w

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- The target transition map from a stage to itself is the identity. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetTransition_id
    (N : Subgroup (FreeGroup X)) [N.Normal] (a : ℕ) :
    foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N
        (le_rfl : a ≤ a) =
      RingHom.id _ := by
  simp only [foxAlgebraicStagePrimePowerTargetTransition,
      foxAlgebraicStageTargetGroupAlgebraCoeffMap_rfl]

omit [DecidableEq X] [Fact (0 < ℓ)] in
/-- Target transition maps compose along the order on prime-power stages. -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetTransition_comp
    (N : Subgroup (FreeGroup X)) [N.Normal] {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab).comp
        (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hbc) =
      foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N (hab.trans hbc) := by
  simp only [foxAlgebraicStagePrimePowerTargetTransition,
      foxAlgebraicStageTargetGroupAlgebraCoeffMap_comp]

/-- The inverse system of finite Fox source quotient group algebras over prime-power stages. -/
def foxAlgebraicStagePrimePowerSourceSystem
    (N : Subgroup (FreeGroup X)) :
    InverseSystem (I := ℕ) where
  X := foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N
  topologicalSpace := fun _ => ⊥
  map := fun {a b} hab => foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
  continuous_map := by
    intro a b hab
    let : TopologicalSpace
        (foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N a) := ⊥
    let : TopologicalSpace
        (foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⊥
    let : DiscreteTopology
        (foxAlgebraicStagePrimePowerSourceGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro a
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (foxAlgebraicStagePrimePowerSourceTransition_id (ℓ := ℓ) (X := X) N a)) x
  map_comp := by
    intro a b c hab hbc
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (foxAlgebraicStagePrimePowerSourceTransition_comp
          (ℓ := ℓ) (X := X) N hab hbc)) x

/-- The inverse system of finite Fox target group algebras over prime-power stages. -/
def foxAlgebraicStagePrimePowerTargetSystem
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    InverseSystem (I := ℕ) where
  X := foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N
  topologicalSpace := fun _ => ⊥
  map := fun {a b} hab => foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
  continuous_map := by
    intro a b hab
    let : TopologicalSpace
        (foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N a) := ⊥
    let : TopologicalSpace
        (foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⊥
    let : DiscreteTopology
        (foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro a
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (foxAlgebraicStagePrimePowerTargetTransition_id (ℓ := ℓ) (X := X) N a)) x
  map_comp := by
    intro a b c hab hbc
    funext x
    exact congrFun
      (congrArg DFunLike.coe
      (foxAlgebraicStagePrimePowerTargetTransition_comp
          (ℓ := ℓ) (X := X) N hab hbc)) x



end

end FoxDifferential
