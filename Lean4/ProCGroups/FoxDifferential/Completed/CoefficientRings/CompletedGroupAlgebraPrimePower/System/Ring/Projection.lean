import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.GroupLike

set_option autoImplicit false

/-!
# Fox differential: prime-power completed group algebra — system — ring — projection

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraProjection_natCast`
  The finite-stage projection preserves natural number casts.
- `primePowerCompletedGroupAlgebraProjection_intCast`
  The finite-stage projection preserves integer casts.
- `primePowerCompletedGroupAlgebraProjection_zero`
  The finite-stage projection sends \(0\) to \(0\).
- `primePowerCompletedGroupAlgebraProjection_add`
  The prime-power finite-stage projection preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection preserves natural number casts. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_natCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℕ) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedGroupAlgebra ℓ G) = n := by
  change (n : PrimePowerCompletedGroupAlgebraStage ℓ G i) = n
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection preserves integer casts. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_intCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℤ) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedGroupAlgebra ℓ G) = n := by
  change (n : PrimePowerCompletedGroupAlgebraStage ℓ G i) = n
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_zero
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedGroupAlgebra ℓ G) = 0 := by
  change (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) = 0
  rfl

omit [Fact (0 < ℓ)] in
/-- The prime-power finite-stage projection preserves addition. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_add
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x + y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x +
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (x + y).1 i) =
    (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- The prime-power finite-stage projection preserves negation. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_neg
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (-x) =
      -primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (-x).1 i) =
    -(show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- The prime-power finite-stage projection preserves subtraction. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_sub
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x - y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x -
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (x - y).1 i) =
    (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) -
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/--
Finite-stage prime-power augmentation is compatible with transition maps and coefficient
reduction.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentation_comp_transition
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2).comp
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)).comp
        (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ j.1) G j.2) := by
  rw [primePowerCompletedGroupAlgebraTransition_eq]
  rw [← RingHom.comp_assoc]
  rw [modNCompletedGroupAlgebraStageAugmentation_comp_coeffMap]
  rw [RingHom.comp_assoc]
  rw [modNCompletedGroupAlgebraStageAugmentation_compatible]

end

end FoxDifferential
