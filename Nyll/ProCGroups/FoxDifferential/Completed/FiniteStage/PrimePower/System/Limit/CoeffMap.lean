/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.System.Limit.Mul

/-!
# Fox differential: prime power — system — limit — coeff map

The principal declarations in this module are:

- `foxAlgebraicStagePrimePowerTargetStageMap_coeffMap`
  Compatibility of target stage maps with coefficient reduction in the completed target group
  algebra.
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


omit [DecidableEq X] in
/--
Compatibility of target stage maps with coefficient reduction in the completed target group
algebra.
-/
theorem foxAlgebraicStagePrimePowerTargetStageMap_coeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    {a b : ℕ} (hab : a ≤ b)
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex
        (foxAlgebraicStageTargetQuotient (X := X) N))
    (x : foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b) :
    modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ a) (m := ℓ ^ b)
        (G := foxAlgebraicStageTargetQuotient (X := X) N) U
        (primePow_dvd_primePow (ℓ := ℓ) hab)
        (modNCompletedGroupAlgebraStageMap (ℓ ^ b)
          (foxAlgebraicStageTargetQuotient (X := X) N) U x) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ a)
        (foxAlgebraicStageTargetQuotient (X := X) N) U
        (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      modNCompletedGroupAlgebraStageCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ b)
          (G := foxAlgebraicStageTargetQuotient (X := X) N) U
          (primePow_dvd_primePow (ℓ := ℓ) hab)
          (modNCompletedGroupAlgebraStageMap (ℓ ^ b)
            (foxAlgebraicStageTargetQuotient (X := X) N) U x) =
        modNCompletedGroupAlgebraStageMap (ℓ ^ a)
          (foxAlgebraicStageTargetQuotient (X := X) N) U
          (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
    rw [modNCompletedGroupAlgebraStageMap_of]
    change modNCompletedGroupAlgebraStageCoeffMap
        (n := ℓ ^ a) (m := ℓ ^ b)
        (G := foxAlgebraicStageTargetQuotient (X := X) N) U
        (primePow_dvd_primePow (ℓ := ℓ) hab)
        (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient
              (foxAlgebraicStageTargetQuotient (X := X) N) U)
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite)
            (G := foxAlgebraicStageTargetQuotient (X := X) N) U
            (QuotientGroup.mk' N w))) =
      modNCompletedGroupAlgebraStageMap (ℓ ^ a)
        (foxAlgebraicStageTargetQuotient (X := X) N) U
        (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
          (MonoidAlgebra.of (ModNCompletedCoeff (ℓ ^ b))
            (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)))
    erw [modNCompletedGroupAlgebraStageCoeffMap_of]
    erw [foxAlgebraicStagePrimePowerTargetTransition_of]
    erw [modNCompletedGroupAlgebraStageMap_of]
    erw [MonoidAlgebra.of_apply]
    rfl
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    rcases ZMod.intCast_surjective r with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hx]
    have ht :
        modNCompletedGroupAlgebraStageCoeffMap
            (n := ℓ ^ a) (m := ℓ ^ b)
            (G := foxAlgebraicStageTargetQuotient (X := X) N) U
            (primePow_dvd_primePow (ℓ := ℓ) hab)
            (modNCompletedGroupAlgebraStageMap (ℓ ^ b)
              (foxAlgebraicStageTargetQuotient (X := X) N) U
              ((algebraMap (ModNCompletedCoeff (ℓ ^ b))
                (foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b)) ↑t)) =
          modNCompletedGroupAlgebraStageMap (ℓ ^ a)
            (foxAlgebraicStageTargetQuotient (X := X) N) U
            (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
              ((algebraMap (ModNCompletedCoeff (ℓ ^ b))
                (foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b)) ↑t)) := by
      simp only [modNCompletedGroupAlgebraStageCoeffMap, modNCompletedGroupRingCoeffMap,
          AlgHom.toRingHom_eq_coe,
  modNCompletedGroupAlgebraStageMap, MonoidAlgebra.mapDomainRingHom, map_intCast,
  foxAlgebraicStagePrimePowerTargetTransition, foxAlgebraicStageTargetGroupAlgebraCoeffMap]
    rw [ht]
    exact (RingHom.map_mul
      (modNCompletedGroupAlgebraStageMap (ℓ ^ a)
        (foxAlgebraicStageTargetQuotient (X := X) N) U)
      (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab
        ((algebraMap (ModNCompletedCoeff (ℓ ^ b))
          (foxAlgebraicStagePrimePowerTargetGroupAlgebra (ℓ := ℓ) (X := X) N b)) ↑t))
      (foxAlgebraicStagePrimePowerTargetTransition (ℓ := ℓ) (X := X) N hab x)).symm




end

end FoxDifferential
