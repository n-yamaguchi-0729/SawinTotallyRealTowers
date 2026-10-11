/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Naturality
import Nyll.ProCGroups.FoxDifferential.Completed.Comparison.QuotientFamily

/-!
# Fox differential: completed — comparison — source projection

The principal declarations in this module are:

- `freeProCZCCompletedFoxBoundary_finiteStageProjection`
  Finite-stage projection of the source-shaped completed Fox boundary map.
- `freeProCZCCompletedFoxBoundary_finiteStageProjection_stage`
  Finite-stage projection of the source-shaped completed Fox boundary map, with generator boundaries
  written in the selected finite pro-`C` quotient.
- `zcFreeFoxCoordinatesMap_finiteStageProjection`
  Componentwise finite-stage projection formula for target maps on completed Fox coordinates.
- `freeProCZCCompletedFoxBoundary_mapTarget_finiteStageProjection_stage`
  Finite-stage projection of target naturality for source-shaped completed Fox boundary maps.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u

section SourceBoundaryProjection

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {X H : Type u} [Fintype X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Finite-stage projection of the source-shaped completed Fox boundary map. -/
theorem freeProCZCCompletedFoxBoundary_finiteStageProjection
    (φ : X → H) (v : ZCFreeFoxCoordinates C (X := X) (H := H))
    (j : ZCCompletedGroupAlgebraIndex C H) :
    zcCompletedGroupAlgebraProjection C H j
        (freeProCZCCompletedFoxBoundary C φ v) =
      ∑ x : X,
        zcCompletedGroupAlgebraProjection C H j (v x) *
          zcCompletedGroupAlgebraProjection C H j (zcGroupLike C H (φ x) - 1) := by
  rw [freeProCZCCompletedFoxBoundary_apply, zcCompletedGroupAlgebraProjection_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [zcCompletedGroupAlgebraProjection, zcCompletedGroupAlgebraProjection_mul,
  zcCompletedGroupAlgebraProjection_sub, zcCompletedGroupAlgebraProjection_groupLike,
  zcCompletedGroupAlgebraProjection_one]

/-- Finite-stage projection of the source-shaped completed Fox boundary map, with generator
boundaries written in the selected finite pro-`C` quotient. -/
theorem freeProCZCCompletedFoxBoundary_finiteStageProjection_stage
    (φ : X → H) (v : ZCFreeFoxCoordinates C (X := X) (H := H))
    (j : ZCCompletedGroupAlgebraIndex C H) :
    zcCompletedGroupAlgebraProjection C H j
        (freeProCZCCompletedFoxBoundary C φ v) =
      ∑ x : X,
        zcCompletedGroupAlgebraProjection C H j (v x) *
          (MonoidAlgebra.of (ModNCompletedCoeff j.1.modulus)
            (CompletedGroupAlgebraQuotientInClass H C j.2)
            (QuotientGroup.mk (φ x)) - 1) := by
  simpa [zcCompletedGroupAlgebraProjection] using
    freeProCZCCompletedFoxBoundary_finiteStageProjection
      (C := C) (X := X) (H := H) φ v j

end SourceBoundaryProjection

section TargetProjectionNaturality

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X H K : Type u} [Fintype X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

omit [Fintype X] in
/-- Componentwise finite-stage projection formula for target maps on completed Fox coordinates. -/
theorem zcFreeFoxCoordinatesMap_finiteStageProjection
    (η : H →ₜ* K)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H))
    (j : ZCCompletedGroupAlgebraIndex C K) (x : X) :
    zcCompletedGroupAlgebraProjection C K j
        (zcFreeFoxCoordinatesMap (X := X) C hC η v x) =
      zcCompletedGroupAlgebraMapStage C hC η j
        (zcCompletedGroupAlgebraProjection C H
          (j.1, completedGroupAlgebraComapIndexInClass
            (G := H) (H := K) C hC η j.2) (v x)) := by
  simp only [zcFreeFoxCoordinatesMap, zcCompletedGroupAlgebraProjection_map]

/-- Finite-stage projection of target naturality for source-shaped completed Fox boundary maps. -/
theorem freeProCZCCompletedFoxBoundary_mapTarget_finiteStageProjection_stage
    (η : H →ₜ* K) (φ : X → H)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H))
    (j : ZCCompletedGroupAlgebraIndex C K) :
    zcCompletedGroupAlgebraProjection C K j
        (zcCompletedGroupAlgebraMap C hC η (freeProCZCCompletedFoxBoundary C φ v)) =
      ∑ x : X,
        zcCompletedGroupAlgebraMapStage C hC η j
          (zcCompletedGroupAlgebraProjection C H
            (j.1, completedGroupAlgebraComapIndexInClass
              (G := H) (H := K) C hC η j.2) (v x)) *
          (MonoidAlgebra.of (ModNCompletedCoeff j.1.modulus)
            (CompletedGroupAlgebraQuotientInClass K C j.2)
            (QuotientGroup.mk (η (φ x))) - 1) := by
  rw [freeProCZCCompletedFoxBoundary_mapTarget]
  rw [freeProCZCCompletedFoxBoundary_finiteStageProjection_stage]
  apply Finset.sum_congr rfl
  intro x _
  rw [zcFreeFoxCoordinatesMap_finiteStageProjection]

end TargetProjectionNaturality

section GenuineFiniteQuotientStage

variable {X : Type u} [DecidableEq X]
variable {N : Subgroup (FreeGroup X)} [N.Normal]

omit [DecidableEq X] in
/-- A quotient bundle certifies that every associated pro-`C` completed group-algebra stage is
actually finite.  This is the canonical finite-stage consumer of
`ZCFiniteStageQuotientBundle`; the unbundled comparison lemmas remain purely algebraic. -/
theorem ZCFiniteStageQuotientBundle.finite_completedGroupAlgebraStage
    (C : ProCGroups.FiniteGroupClass.{u})
    (B : ZCFiniteStageQuotientBundle N)
    (j : B.Index C) :
    letI : TopologicalSpace B.Target := B.targetTopology
    letI : IsTopologicalGroup B.Target := B.targetIsTopologicalGroup
    Finite (ZCCompletedGroupAlgebraStage C B.Target j) := by
  let : TopologicalSpace B.Target := B.targetTopology
  let : IsTopologicalGroup B.Target := B.targetIsTopologicalGroup
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  exact
    finite_modNCompletedGroupAlgebraStageInClass
      (n := j.1.modulus) (G := B.Target) C j.2

end GenuineFiniteQuotientStage

end

end FoxDifferential
