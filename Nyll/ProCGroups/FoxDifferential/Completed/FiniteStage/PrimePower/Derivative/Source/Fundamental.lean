/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Derivative.Source.GroupLike

/-!
# Fox differential: prime power — derivative — source — fundamental

The principal declarations in this module are:

- `ppCompletedGAFoxDerivToTarget_of_fundFormula_proj`
  The completed-target Fox fundamental formula for a group-like source element after projection to
  one completed target stage.
- `ppCompletedGAFoxDerivToTarget_of_fundFormula`
  The completed-target Fox fundamental formula for a group-like source element.
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
The completed-target Fox fundamental formula for a group-like source element after projection to
one completed target stage.
-/
theorem ppCompletedGAFoxDerivToTarget_of_fundFormula_proj
    [Fintype X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (w : FreeGroup X)
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
        (primePowerCompletedGroupAlgebraOf (ell := ℓ)
          (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1) =
      ∑ i : X,
        primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
            (ℓ := ℓ) (X := X) N hfinite i
            (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w)) *
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
            (primePowerCompletedGroupAlgebraOf (ell := ℓ)
              (H := foxAlgebraicStageTargetQuotient (X := X) N)
              (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  have hstage := congrArg
    (fun z =>
      (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
          (foxAlgebraicStageTargetQuotient (X := X) N) j.2 z :
        PrimePowerCompletedGroupAlgebraStage ℓ
          (foxAlgebraicStageTargetQuotient (X := X) N) j))
    (foxAlgebraicStageDerivative_fundamental_formula
      (X := X) (N := N) (n := ℓ ^ j.1) w)
  simp_rw [primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget_of_projection,
    primePowerCompletedGroupAlgebraProjection_sub,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_one]
  simp only [map_sub, map_sum, map_mul, map_one] at hstage
  simp_rw [modNCompletedGroupAlgebraStageMap_of] at hstage
  simp only [QuotientGroup.mk'_apply]
  change @Eq
    (ModNCompletedGroupAlgebraStage (ℓ ^ j.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) j.2) _ _
  convert hstage using 1 <;> rfl

omit [Fact (0 < ℓ)] in
/-- The completed-target Fox fundamental formula for a group-like source element. -/
theorem ppCompletedGAFoxDerivToTarget_of_fundFormula
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
    primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1 =
      ∑ i : X,
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) *
          (primePowerCompletedGroupAlgebraOf (ell := ℓ)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro j
  change primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
      (primePowerCompletedGroupAlgebraOf (ell := ℓ)
        (H := foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) - 1) =
    primePowerCompletedGroupAlgebraProjection
      (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
      (∑ i : X,
        primePowerCompletedGroupAlgebraFreeFoxDerivativeToCompletedTarget
          (ℓ := ℓ) (X := X) N hfinite i
          (primePowerCompletedGroupAlgebraOf (ell := ℓ) (H := FreeGroup X) w) *
          (primePowerCompletedGroupAlgebraOf (ell := ℓ)
            (H := foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1))
  rw [ppCompletedGAFoxDerivToTarget_of_fundFormula_proj
    (ℓ := ℓ) (X := X) N hfinite w j]
  have hsum
      (f : X → PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)) :
      primePowerCompletedGroupAlgebraProjection
          (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j
          (∑ i : X, f i) =
        ∑ i : X,
          primePowerCompletedGroupAlgebraProjection
            (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) j (f i) := by
    classical
    refine Finset.induction_on (s := Finset.univ) ?_ ?_
    · simp only [Finset.sum_empty, InverseSystem.projection_apply,
        coe_zero_primePowerCompletedGroupAlgebra, Pi.zero_apply]
      rfl
    · intro a s has ih
      rw [Finset.sum_insert has, Finset.sum_insert has,
        primePowerCompletedGroupAlgebraProjection_add, ih]
  rw [hsum]
  rfl



end

end FoxDifferential
