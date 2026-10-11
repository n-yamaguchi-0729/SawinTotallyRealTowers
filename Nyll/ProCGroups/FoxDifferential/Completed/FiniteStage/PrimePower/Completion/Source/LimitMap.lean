/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Index

/-!
# Fox differential: prime power — completion — source — limit map

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit`
  The additive map from the completed source group algebra to the prime-power finite-stage source
  inverse limit.
- `primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_one`
  The completed-source-to-finite-stage-limit map preserves \(1\).
- `primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_mul`
  The completed-source-to-finite-stage-limit map preserves multiplication.
- `primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_projection`
  Projecting the completed-source-to-finite-stage-limit map gives the corresponding finite-stage
  limit coordinate.
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
The additive map from the completed source group algebra to the prime-power finite-stage source
inverse limit.
-/
def primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      FoxAlgebraicStagePrimePowerSourceLimit (ℓ := ℓ) (X := X) N where
  toFun z :=
    ⟨fun a =>
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) z,
      by
        intro a b hab
        change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (b, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
                  z) =
          primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) z
        exact z.2
          (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
          (b, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
          ⟨hab,
            foxAlgebraicStagePrimePowerSourceCompletedIndex_mono
              (ℓ := ℓ) (X := X) N hfinite hab⟩⟩
  map_zero' := by
    apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        (0 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 0
    exact primePowerCompletedGroupAlgebraProjection_zero (ℓ := ℓ) (G := FreeGroup X) _
  map_add' x y := by
    apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
    funext a
    change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        (x + y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) x +
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) y
    exact primePowerCompletedGroupAlgebraProjection_add (ℓ := ℓ) (G := FreeGroup X) _ x y

omit [DecidableEq X] in
/-- The completed-source-to-finite-stage-limit map preserves \(1\). -/
@[simp]
theorem primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_one
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite
        (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 1 := by
  apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (1 : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) = 1
  exact primePowerCompletedGroupAlgebraProjection_one (ℓ := ℓ) (G := FreeGroup X) _

omit [DecidableEq X] in
/-- The completed-source-to-finite-stage-limit map preserves multiplication. -/
@[simp 900]
theorem primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_mul
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (x y : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) :
    primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite (x * y) =
      primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
          (ℓ := ℓ) (X := X) N hfinite x *
        primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
          (ℓ := ℓ) (X := X) N hfinite y := by
  apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  change primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (x * y) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) x *
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) y
  exact primePowerCompletedGroupAlgebraProjection_mul (ℓ := ℓ) (G := FreeGroup X) _ x y

omit [DecidableEq X] in
/--
Projecting the completed-source-to-finite-stage-limit map gives the corresponding finite-stage
limit coordinate.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    (foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N).projection a
        (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
          (ℓ := ℓ) (X := X) N hfinite z) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a) z := rfl

omit [DecidableEq X] in
/--
The restriction from the genuine completed group algebra to the completed-free-derivative source
subsystem is surjective. This stays inside completed group algebras and inverse limits: each
source stage is one of the finite completed group-algebra stages, and the stage projections are
already surjective.
-/
theorem primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit_surjective
    [Fact (0 < ℓ)]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a))) :
    Function.Surjective
      (primePowerCompletedGroupAlgebraToFoxAlgebraicStagePrimePowerSourceLimit
        (ℓ := ℓ) (X := X) N hfinite) := by
  classical
  let T := foxAlgebraicStagePrimePowerSourceSystem (ℓ := ℓ) (X := X) N
  let S := primePowerCompletedGroupAlgebraSystem ℓ (FreeGroup X)
  let ψ : ∀ a : ℕ,
      PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) → T.X a :=
    fun a z =>
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        z
  have hψcont : ∀ a : ℕ, Continuous (ψ a) := by
    intro a
    change Continuous
      (S.projection
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite a))
    exact S.continuous_projection
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex
        (ℓ := ℓ) (X := X) N hfinite a)
  have hψcompat : T.CompatibleMaps ψ := by
    intro a b hab
    funext z
    change foxAlgebraicStagePrimePowerSourceTransition (ℓ := ℓ) (X := X) N hab
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (b, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
          z) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
        z
    exact z.2
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a)
      (b, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b)
      ⟨hab,
        foxAlgebraicStagePrimePowerSourceCompletedIndex_mono
          (ℓ := ℓ) (X := X) N hfinite hab⟩
  have hψsurj : ∀ a : ℕ, Function.Surjective (ψ a) := by
    intro a
    change Function.Surjective
      (primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite a))
    exact primePowerCompletedGroupAlgebraProjection_surjective
      (ℓ := ℓ) (G := FreeGroup X)
      (a, foxAlgebraicStagePrimePowerSourceCompletedIndex
        (ℓ := ℓ) (X := X) N hfinite a)
  let : ∀ a : ℕ, TopologicalSpace (T.X a) := fun a => T.topologicalSpace a
  let : ∀ a : ℕ, DiscreteTopology (T.X a) := fun _ => ⟨rfl⟩
  let : ∀ a : ℕ, T2Space (T.X a) := fun _ => inferInstance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), TopologicalSpace (S.X i) :=
    fun i => S.topologicalSpace i
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), DiscreteTopology (S.X i) :=
    fun _ => ⟨rfl⟩
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), CompactSpace (S.X i) :=
    fun i => by
      let : Finite (S.X i) := by
        dsimp [S, primePowerCompletedGroupAlgebraSystem]
        infer_instance
      let : Fintype (S.X i) := Fintype.ofFinite _
      infer_instance
  let : ∀ i : PrimePowerCompletedGroupAlgebraIndex (FreeGroup X), T2Space (S.X i) :=
    fun _ => inferInstance
  let : CompactSpace (PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) :=
    inferInstance
  let : T2Space (PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) :=
    S.t2Space_inverseLimit
  have hdirNat : Directed (· ≤ ·) (id : ℕ → ℕ) := by
    intro a b
    exact ⟨max a b, le_max_left _ _, le_max_right _ _⟩
  have hlift : Function.Surjective (T.inverseLimitLift ψ hψcompat) :=
    T.surjective_inverseLimitLift ψ hψcont hψcompat hψsurj hdirNat
  intro y
  rcases hlift y with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  apply foxAlgebraicStagePrimePowerSourceLimitToFamily_injective (ℓ := ℓ) (X := X) N
  funext a
  have hcomponent := congrArg (T.projection a) hz
  change ψ a z = T.projection a y
  exact
    (T.projection_inverseLimitLift_apply ψ hψcompat a z).symm.trans
      hcomponent

omit [DecidableEq X] in
/--
The compatibility between source-stage augmentation and completed-group-algebra augmentation
after projecting to a finite Fox source stage.
-/
@[simp]
theorem foxCommutatorPowerSourceGroupAlgebraAugmentation_projection_eq_completed
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X)) (a : ℕ) :
    foxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N (ℓ ^ a)
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
          (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite a) z) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := FreeGroup X)
        (a, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
          N hfinite a)
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := FreeGroup X) z) := by
  rw [primePowerCompletedCoeffProjection_augmentation]
  rfl



end

end FoxDifferential
