/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.CompletedSource

/-!
# Fox differential: finite stage — prime power — derivative — completed target

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget`
  The completed source Fox derivative, mapped from the finite-stage target limit into the completed
  group algebra of the target quotient.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection`
  Projecting the completed-target Fox derivative gives the corresponding finite-stage derivative.
- `primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_unique`
  The completed-target prime-power Fox derivative is uniquely determined by all completed target
  finite-stage projection formulas.
- `ppCompletedGAFoxDerivToTarget_fundFormula_proj`
  The completed-target fundamental formula after projection to one completed target stage.
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


/--
The completed source Fox derivative, mapped from the finite-stage target limit into the
completed group algebra of the target quotient.
-/
def primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N) :=
  (foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
    ℓ (X := X) N).comp
    (primePowerCompletedGroupAlgebraFreeFoxDerivative
      (ℓ := ℓ) (X := X) N hfinite i)

omit [Fact (0 < ℓ)] in
/--
Projecting the completed-target Fox derivative gives the corresponding finite-stage derivative.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X) (z : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i z) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ j.1) i
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) := by
  rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget,
    AddMonoidHom.comp_apply,
    foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection,
    primePowerCompletedGroupAlgebraFreeFoxDerivative_projection]

omit [Fact (0 < ℓ)] in
/--
The completed-target prime-power Fox derivative is uniquely determined by all completed target
finite-stage projection formulas.
-/
theorem primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_unique
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (i : X)
    (f : PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) →+
      PrimePowerCompletedGroupAlgebra ℓ (foxAlgebraicStageTargetQuotient (X := X) N))
    (hf : ∀ z
      (j : PrimePowerCompletedGroupAlgebraIndex (foxAlgebraicStageTargetQuotient (X := X) N)),
      primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j (f z) =
        modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
          (foxAlgebraicStageTargetQuotient (X := X) N) j.2
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N (ℓ ^ j.1) i
            (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
              (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
                N hfinite j.1) z))) :
    f = primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
      (ℓ := ℓ) (X := X) N hfinite i := by
  apply AddMonoidHom.ext
  intro z
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro j
  change
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j (f z) =
      primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i z)
  rw [hf, primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_projection]

omit [Fact (0 < ℓ)] in
/-- The completed-target fundamental formula after projection to one completed target stage. -/
theorem ppCompletedGAFoxDerivToTarget_fundFormula_proj
    [Fintype X]
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
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z) -
          algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
            (foxAlgebraicStageTargetGroupAlgebra (X := X) N (ℓ ^ j.1))
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N (ℓ ^ j.1)
              (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
                (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
                  N hfinite j.1) z))) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i z) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have hstage := congrArg
    (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) j.2)
    (primePowerCompletedGroupAlgebraFreeFoxDerivative_fundamental_formula_projection
      (ℓ := ℓ) (X := X) N hfinite z j.1)
  rw [hstage, map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul]
  congr 1
  rw [map_sub, modNCompletedGroupAlgebraStageMap_of, map_one,
    primePowerCompletedGroupAlgebraProjection_sub,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_one]
  simp only [MonoidAlgebra.single, QuotientGroup.mk'_apply, MonoidAlgebra.of,
    MonoidHom.coe_mk]
  rfl

omit [Fact (0 < ℓ)] in
/--
The projected completed-target fundamental formula with the augmentation term written through
the target-stage algebra map.
-/
theorem ppCompletedGAFoxDerivToTarget_fundFormula_proj_algebraMap
    [Fintype X]
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
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) -
      algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
        (PrimePowerCompletedGroupAlgebraStage ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N) j)
        (foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i z) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have h :=
    ppCompletedGAFoxDerivToTarget_fundFormula_proj
      (ℓ := ℓ) (X := X) N hfinite z j
  rw [map_sub, modNCompletedGroupAlgebraStageMap_algebraMap] at h
  simpa using h

omit [Fact (0 < ℓ)] in
/--
After projection to the completed target, the fundamental formula uses the source augmentation
computed in the completed group algebra.
-/
theorem primePowerCompletedTarget_fundamentalFormula_projection_completedAugmentation
    [Fintype X]
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
    modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) j.2
        (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N (ℓ ^ j.1)
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := FreeGroup X)
            (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
              N hfinite j.1) z)) -
      algebraMap (ModNCompletedCoeff (ℓ ^ j.1))
        (PrimePowerCompletedGroupAlgebraStage ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N) j)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := FreeGroup X)
          (j.1, foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
            N hfinite j.1)
          (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := FreeGroup X) z)) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i z) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have h :=
    ppCompletedGAFoxDerivToTarget_fundFormula_proj_algebraMap
      (ℓ := ℓ) (X := X) N hfinite z j
  rw [foxCommutatorPowerSourceGroupAlgebraAugmentation_projection_eq_completed
    (ℓ := ℓ) (X := X) N hfinite z j.1] at h
  exact h



end

end FoxDifferential
