/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.TargetQuotient.Basic
import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.GroupLike

/-!
# Fox differential: completed — differential module — target quotient — stage map

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMapStage_targetQuotient_transition_source`
  At a completed finite stage of \(F/N\), the completed map induced by \(F \to F/N\) agrees with
  first projecting to the completed free derivative source finite quotient and then using the
  completed free derivative natural finite-stage group-algebra map.
- `primePowerCompletedGAProj_map_targetQuotient_eq_freeDerivativeSource`
  The target finite-stage projection of the completed quotient map can be computed using the
  completed free derivative source projection at the same prime-power exponent.
- `primePowerCompletedGroupAlgebraMap_targetQuotient_of`
  The target-quotient prime-power map sends a group-like basis element to the basis element
  supported at its target-quotient image.
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

omit [DecidableEq X] in
/--
At a completed finite stage of \(F/N\), the completed map induced by \(F \to F/N\) agrees with
first projecting to the completed free derivative source finite quotient and then using the
completed free derivative natural finite-stage group-algebra map.
-/
theorem primePowerCompletedGroupAlgebraMapStage_targetQuotient_transition_source
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N))
    (x : PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
      (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
        (ℓ := ℓ) (X := X) N hfinite j.1)) :
    primePowerCompletedGroupAlgebraMapStage
        (ℓ := ℓ) (G := FreeGroup X)
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X)
          (show
            (j.1, completedGroupAlgebraComapIndex
              (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) ≤
              (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1) from
            ⟨le_rfl,
              foxAlgebraicStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
                (ℓ := ℓ) (X := X) N hfinite j⟩) x) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1) x) := by
  let hidx :
      (j.1, completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) ≤
        (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) :=
    ⟨le_rfl,
      foxAlgebraicStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
        (ℓ := ℓ) (X := X) N hfinite j⟩
  let leftMap :
      PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
          (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
            (ℓ := ℓ) (X := X) N hfinite j.1) →+*
        PrimePowerCompletedGroupAlgebraStage ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N) j :=
    (primePowerCompletedGroupAlgebraMapStage
      (ℓ := ℓ) (G := FreeGroup X)
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j).comp
      (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X) hidx)
  let rightMap :
      PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
          (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
            (ℓ := ℓ) (X := X) N hfinite j.1) →+*
        PrimePowerCompletedGroupAlgebraStage ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N) j :=
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) j.2).comp
      (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1))
  change leftMap x = rightMap x
  have hmaps : leftMap = rightMap := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
      change leftMap
          ((algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
            (PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
              (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1)))
            (t : ModNCompletedCoeff (ℓ ^ j.1))) =
        rightMap
          ((algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
            (PrimePowerCompletedGroupAlgebraStage ℓ (FreeGroup X)
              (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1)))
            (t : ModNCompletedCoeff (ℓ ^ j.1)))
      simp only [map_intCast]
    · intro q
      rcases QuotientGroup.mk'_surjective
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) q with
        ⟨w, rfl⟩
      let qSource :
          _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
            (foxAlgebraicStagePrimePowerSourceCompletedIndex
              (ℓ := ℓ) (X := X) N hfinite j.1) :=
        QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1)) w
      have hsourceComap :
          (((OrderDual.ofDual
              (foxAlgebraicStagePrimePowerSourceCompletedIndex
                (ℓ := ℓ) (X := X) N hfinite j.1)).1 :
                OpenNormalSubgroup (FreeGroup X)) : Subgroup (FreeGroup X)) ≤
            (((OrderDual.ofDual
              (completedGroupAlgebraComapIndex
                (G := FreeGroup X)
                (H := foxAlgebraicStageTargetQuotient (X := X) N)
                (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
                j.2)).1 : OpenNormalSubgroup (FreeGroup X)) : Subgroup (FreeGroup X)) := by
        change
          completedGroupAlgebraComapIndex
              (G := FreeGroup X)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2 ≤
            foxAlgebraicStagePrimePowerSourceCompletedIndex
              (ℓ := ℓ) (X := X) N hfinite j.1
        exact
          foxAlgebraicStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
            (ℓ := ℓ) (X := X) N hfinite j
      let qComap :
          _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
            (completedGroupAlgebraComapIndex
              (G := FreeGroup X)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) :=
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := FreeGroup X)
          (U := OrderDual.ofDual
            (completedGroupAlgebraComapIndex
              (G := FreeGroup X)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2))
          (V := OrderDual.ofDual
            (foxAlgebraicStagePrimePowerSourceCompletedIndex
              (ℓ := ℓ) (X := X) N hfinite j.1)) hsourceComap) qSource
      change
        leftMap
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
              (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                (foxAlgebraicStagePrimePowerSourceCompletedIndex
                  (ℓ := ℓ) (X := X) N hfinite j.1)) qSource) =
          rightMap
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
              (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                (foxAlgebraicStagePrimePowerSourceCompletedIndex
                  (ℓ := ℓ) (X := X) N hfinite j.1)) qSource)
      dsimp [leftMap, rightMap]
      change
        primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := FreeGroup X)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j
            (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X)
              hidx
              (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
                (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                  (foxAlgebraicStagePrimePowerSourceCompletedIndex
                    (ℓ := ℓ) (X := X) N hfinite j.1))
                qSource)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
            (foxAlgebraicStageTargetQuotient (X := X) N) j.2
            (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
              (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
                (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                  (foxAlgebraicStagePrimePowerSourceCompletedIndex
                    (ℓ := ℓ) (X := X) N hfinite j.1))
                qSource))
      erw [primePowerCompletedGroupAlgebraTransition_of]
      change
        primePowerCompletedGroupAlgebraMapStage
            (ℓ := ℓ) (G := FreeGroup X)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j
            (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
              (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient (FreeGroup X)
                (completedGroupAlgebraComapIndex
                  (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
                  (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2))
              qComap) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
            (foxAlgebraicStageTargetQuotient (X := X) N) j.2
            (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
              (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ j.1))
                (FreeGroup X ⧸
                  foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1))
                qSource))
      rw [primePowerCompletedGroupAlgebraMapStage_of,
        foxCommutatorPowerGroupAlgebraMap_of,
        modNCompletedGroupAlgebraStageMap_of]
      rfl
  rw [hmaps]

omit [DecidableEq X] in
/--
The target finite-stage projection of the completed quotient map can be computed using the
completed free derivative source projection at the same prime-power exponent.
-/
theorem primePowerCompletedGAProj_map_targetQuotient_eq_freeDerivativeSource
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraMap
          (ℓ := ℓ) (G := FreeGroup X)
          (H := foxAlgebraicStageTargetQuotient (X := X) N)
          (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) z) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
              (ℓ := ℓ) (X := X) N hfinite j.1) z)) := by
  let hidx :
      (j.1, completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) ≤
        (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) :=
    ⟨le_rfl,
      foxAlgebraicStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
        (ℓ := ℓ) (X := X) N hfinite j⟩
  rw [primePowerCompletedGroupAlgebraProjection_map]
  have hz := z.2
    (j.1, completedGroupAlgebraComapIndex
      (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
      (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2)
    (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
      (ℓ := ℓ) (X := X) N hfinite j.1) hidx
  change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := FreeGroup X) hidx
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) z) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
      (j.1, completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2) z at hz
  rw [← hz]
  exact
    primePowerCompletedGroupAlgebraMapStage_targetQuotient_transition_source
      (ℓ := ℓ) (X := X) N hfinite j
      (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
        (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex
          (ℓ := ℓ) (X := X) N hfinite j.1) z)

omit [DecidableEq X] in
/--
The target-quotient prime-power map sends a group-like basis element to the basis element supported
at its target-quotient image.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_targetQuotient_of
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (w : FreeGroup X) :
    primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
        (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) =
      primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := by
  rw [primePowerCompletedGroupAlgebraMap_of]
  rfl


end

end FoxDifferential
