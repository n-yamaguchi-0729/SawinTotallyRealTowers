import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Module

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power completed group algebra — augmentation

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraAugmentation`
  The prime-power completed group algebra carries a canonical augmentation to the corresponding
  coefficient inverse limit.
- `primePowerCompletedCoeffProjection_augmentation`
  Projecting the prime-power completed augmentation to a coefficient stage agrees with the
  corresponding finite-stage augmentation.
- `primePowerCompletedGroupAlgebraStageAugmentation_eq_of_same_exponent`
  Stagewise augmentations of a completed group-algebra element are independent of the
  finite-quotient component once the prime-power exponent is fixed.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The prime-power completed group algebra carries a canonical augmentation to the corresponding
coefficient inverse limit.
-/
def primePowerCompletedGroupAlgebraAugmentation :
    PrimePowerCompletedGroupAlgebra ℓ G → PrimePowerCompletedCoeff ℓ G := by
  intro x
  refine ⟨fun i => ?_, ?_⟩
  · exact modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2 (x.1 i)
  · intro i j hij
    calc
      modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ j.1) G j.2 (x.1 j))
        =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij (x.1 j)) := by
          symm
          exact congrFun
            (congrArg DFunLike.coe
              (primePowerCompletedGroupAlgebraStageAugmentation_comp_transition
                (ℓ := ℓ) (G := G) hij)) (x.1 j)
      _ =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2 (x.1 i) := by
          have hx :
              primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij (x.1 j) = x.1 i :=
            x.2 i j hij
          exact congrArg (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2) hx

omit [Fact (0 < ℓ)] in
/--
Projecting the prime-power completed augmentation to a coefficient stage agrees with the
corresponding finite-stage augmentation.
-/
@[simp]
theorem primePowerCompletedCoeffProjection_augmentation
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x) := rfl

omit [Fact (0 < ℓ)] in
/--
Stagewise augmentations of a completed group-algebra element are independent of the
finite-quotient component once the prime-power exponent is fixed.
-/
theorem primePowerCompletedGroupAlgebraStageAugmentation_eq_of_same_exponent
    (a : ℕ) (U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ a) G U
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) (a, U) x) =
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ a) G V
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) (a, V) x) := by
  change
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, U)
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, V)
        (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x)
  exact primePowerCompletedCoeffProjection_eq_of_same_exponent
    (ℓ := ℓ) (G := G) a U V
    (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x)

end

end FoxDifferential
