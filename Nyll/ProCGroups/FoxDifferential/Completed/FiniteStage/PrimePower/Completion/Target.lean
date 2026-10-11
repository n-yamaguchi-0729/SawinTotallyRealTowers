/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.AddCommGroup
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.CoeffMap

/-!
# Fox differential: finite stage — prime power — completion — target

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra`
  The canonical additive map from the prime-power target inverse limit to the completed group
  algebra of the finite-stage target quotient.
- `foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection`
  Projecting the map from the prime-power target limit gives the corresponding completed target
  group-algebra coordinate.
- `foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_one`
  The target-limit-to-completed-group-algebra map preserves \(1\).
- `foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_mul`
  The target-limit-to-completed-group-algebra map preserves multiplication.
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
The canonical additive map from the prime-power target inverse limit to the completed group
algebra of the finite-stage target quotient.
-/
def foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)] :
    AddMonoidHom
      (FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
      (PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)) where
  toFun z :=
    ⟨fun i =>
        modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
          (foxAlgebraicStageTargetQuotient (X := X) N) i.2
          ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 z),
      by
        intro i j hij
        change primePowerCompletedGroupAlgebraTransition
            (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) hij
            (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
              (foxAlgebraicStageTargetQuotient (X := X) N) j.2
              ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
            (foxAlgebraicStageTargetQuotient (X := X) N) i.2
            ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 z)
        rw [primePowerCompletedGroupAlgebraTransition_eq, RingHom.comp_apply]
        have hstage := congrFun
          (congrArg DFunLike.coe
            (modNCompletedGroupAlgebraStageMap_compatible
          (n := ℓ ^ j.1) (G := foxAlgebraicStageTargetQuotient (X := X) N)
          (U := i.2) (V := j.2) hij.2))
          ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z)
        change modNCompletedGroupAlgebraTransition (ℓ ^ j.1)
            (foxAlgebraicStageTargetQuotient (X := X) N) hij.2
            (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
              (foxAlgebraicStageTargetQuotient (X := X) N) j.2
              ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection j.1 z)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
            (foxAlgebraicStageTargetQuotient (X := X) N) i.2
            ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection
              j.1 z) at hstage
        rw [hstage]
        have hcoeffMap :
            modNCompletedGroupAlgebraStageCoeffMap
                (n := ℓ ^ i.1) (m := ℓ ^ j.1)
                (G := foxAlgebraicStageTargetQuotient (X := X) N) i.2
                (primePow_dvd_primePow (ℓ := ℓ) hij.1)
                (modNCompletedGroupAlgebraStageMap (ℓ ^ j.1)
                  (foxAlgebraicStageTargetQuotient (X := X) N) i.2
                  ((foxAlgebraicStagePrimePowerTargetSystem
                    (ℓ := ℓ) (X := X) N).projection j.1 z)) =
              modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
                (foxAlgebraicStageTargetQuotient (X := X) N) i.2
                (foxAlgebraicStagePrimePowerTargetTransition
                  (ℓ := ℓ) (X := X) N hij.1
                  ((foxAlgebraicStagePrimePowerTargetSystem
                    (ℓ := ℓ) (X := X) N).projection j.1 z)) :=
          foxAlgebraicStagePrimePowerTargetStageMap_coeffMap
            (ℓ := ℓ) (X := X) N hij.1 i.2
            ((foxAlgebraicStagePrimePowerTargetSystem
              (ℓ := ℓ) (X := X) N).projection j.1 z)
        exact hcoeffMap.trans
          (congrArg
            (modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
              (foxAlgebraicStageTargetQuotient (X := X) N) i.2)
            ((foxAlgebraicStagePrimePowerTargetSystem
              (ℓ := ℓ) (X := X) N).projection_compatible z i.1 j.1 hij.1))⟩
  map_zero' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ
      (foxAlgebraicStageTargetQuotient (X := X) N)).ext
    intro i
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1
          (0 : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)) = 0
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        (0 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1) = 0
    exact map_zero _
  map_add' x y := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ
      (foxAlgebraicStageTargetQuotient (X := X) N)).ext
    intro i
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 (x + y)) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) +
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
    change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) +
          (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
            (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) +
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
    exact map_add _ _ _

omit [DecidableEq X] in
/--
Projecting the map from the prime-power target limit gives the corresponding completed target
group-algebra coordinate.
-/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_projection
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (z : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)
    (i : PrimePowerCompletedGroupAlgebraIndex (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraProjection
        (ℓ := ℓ) (G := foxAlgebraicStageTargetQuotient (X := X) N) i
        (foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
          ℓ (X := X) N z) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
        (foxAlgebraicStageTargetQuotient (X := X) N) i.2
        ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 z) := rfl

omit [DecidableEq X] in
/-- The target-limit-to-completed-group-algebra map preserves \(1\). -/
@[simp]
theorem foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_one
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)] :
    foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N
        (1 : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) =
      (1 : PrimePowerCompletedGroupAlgebra ℓ
        (foxAlgebraicStageTargetQuotient (X := X) N)) := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro i
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1
        (1 : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N)) = 1
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      (1 : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1) = 1
  exact map_one _

omit [DecidableEq X] in
/-- The target-limit-to-completed-group-algebra map preserves multiplication. -/
@[simp 900]
theorem foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra_mul
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (x y : FoxAlgebraicStagePrimePowerTargetLimit (ℓ := ℓ) (X := X) N) :
    foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
        ℓ (X := X) N (x * y) =
      foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
          ℓ (X := X) N x *
        foxAlgebraicStagePrimePowerTargetLimitToCompletedGroupAlgebra
          ℓ (X := X) N y := by
  apply (primePowerCompletedGroupAlgebraSystem ℓ
    (foxAlgebraicStageTargetQuotient (X := X) N)).ext
  intro i
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 (x * y)) =
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) *
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
  change modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
        (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) *
        (show foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N i.1 from
          (foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)) =
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 x) *
    modNCompletedGroupAlgebraStageMap (ℓ ^ i.1)
      (foxAlgebraicStageTargetQuotient (X := X) N) i.2
      ((foxAlgebraicStagePrimePowerTargetSystem (ℓ := ℓ) (X := X) N).projection i.1 y)
  exact map_mul _ _ _



end

end FoxDifferential
