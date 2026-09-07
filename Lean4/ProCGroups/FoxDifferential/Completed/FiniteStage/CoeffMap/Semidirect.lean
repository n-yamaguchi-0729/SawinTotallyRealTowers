import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.Augmentation

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — coeff map — semidirect

The principal declarations in this module are:

- `foxAlgebraicStageSemidirectCoeffMap`
  Coefficient-reduction map on finite-stage semidirect Fox targets.
- `foxAlgebraicStageSemidirectCoeffMap_lift`
  The finite-stage semidirect coefficient map carries the lift at modulus \(m\) to the lift at
  modulus \(n\).
- `foxAlgebraicStageDerivative_coeffMap`
  Finite-stage Fox derivative coordinates commute with coefficient reduction.
- `foxAlgebraicStageGroupAlgebraDerivative_powerCoeff_natural`
  Finite-stage group-algebra derivative coordinates commute with source transition and coefficient
  reduction.
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


variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]

/-- Coefficient-reduction map on finite-stage semidirect Fox targets. -/
def foxAlgebraicStageSemidirectCoeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    FoxAlgebraicStageSemidirect (X := X) N m₀ →*
      FoxAlgebraicStageSemidirect (X := X) N n₀ where
  toFun a :=
    { left := fun i => foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm (a.left i)
      right := a.right }
  map_one' := by
    apply FoxAlgebraicStageSemidirect.ext
    · funext i
      simp only [FoxAlgebraicStageSemidirect.one_left, Pi.zero_apply, map_zero]
    · rfl
  map_mul' a b := by
    apply FoxAlgebraicStageSemidirect.ext
    · funext i
      have hright :
          foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
              (MonoidAlgebra.single a.right (1 : ModNCompletedCoeff m₀)) =
            MonoidAlgebra.single a.right (1 : ModNCompletedCoeff n₀) := by
        simpa only [map_one] using
          foxAlgebraicStageTargetGroupAlgebraCoeffMap_single_apply
            (X := X) N hnm a.right (1 : ModNCompletedCoeff m₀)
      simp only [FoxAlgebraicStageSemidirect.mul_left, MonoidAlgebra.of_apply, Pi.add_apply,
          Pi.smul_apply,
  smul_eq_mul, map_add, map_mul, hright]
    · simp only [FoxAlgebraicStageSemidirect.mul_right]

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
The finite-stage semidirect coefficient map carries the lift at modulus \(m\) to the lift at
modulus \(n\).
-/
theorem foxAlgebraicStageSemidirectCoeffMap_lift
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm
        (foxAlgebraicStageLift (X := X) N m₀ w) =
      foxAlgebraicStageLift (X := X) N n₀ w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [foxAlgebraicStageLift, QuotientGroup.mk'_apply, map_one]
  | of x =>
      apply FoxAlgebraicStageSemidirect.ext
      · funext i
        by_cases hix : i = x
        · subst hix
          simp only [foxAlgebraicStageSemidirectCoeffMap, foxAlgebraicStageLift,
              QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of, MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_same, map_one]
        · simp only [foxAlgebraicStageSemidirectCoeffMap, foxAlgebraicStageLift,
            QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of, MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_of_ne hix, map_zero]
      · rfl
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Finite-stage Fox derivative coordinates commute with coefficient reduction. -/
theorem foxAlgebraicStageDerivative_coeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (i : X) (w : FreeGroup X) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (foxAlgebraicStageDerivative (X := X) N m₀ i w) =
      foxAlgebraicStageDerivative (X := X) N n₀ i w := by
  have h :=
    congrArg FoxAlgebraicStageSemidirect.left
      (foxAlgebraicStageSemidirectCoeffMap_lift (X := X) N hnm w)
  simpa [foxAlgebraicStageDerivative, foxAlgebraicStageDerivativeVector,
    foxAlgebraicStageSemidirectCoeffMap] using congrFun h i

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
Finite-stage group-algebra derivative coordinates commute with source transition and coefficient
reduction.
-/
theorem foxAlgebraicStageGroupAlgebraDerivative_powerCoeff_natural
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (i : X)
    (x : MonoidAlgebra (ModNCompletedCoeff m₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (foxAlgebraicStageGroupAlgebraDerivative (X := X) N m₀ i x) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n₀ i
        (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N m₀ i x) =
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n₀ i
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) q with ⟨w, rfl⟩
    rw [foxAlgebraicStageGroupAlgebraDerivative_of,
      foxAlgebraicStagePowerSourceGroupAlgebraMap_of,
      foxAlgebraicStageGroupAlgebraDerivative_of,
      foxAlgebraicStageDerivative_coeffMap]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    have htargetScalar :
        foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
            (MonoidAlgebra.single
              (1 : foxAlgebraicStageTargetQuotient (X := X) N) a) =
          MonoidAlgebra.single
            (1 : foxAlgebraicStageTargetQuotient (X := X) N)
            (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
      exact foxAlgebraicStageTargetGroupAlgebraCoeffMap_single_apply
        (X := X) N hnm 1 a
    have hsourceScalar :
        foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm
            (MonoidAlgebra.single
              (1 : FreeGroup X ⧸
                foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) a) =
          MonoidAlgebra.single
            (1 : FreeGroup X ⧸
              foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
            (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
      simpa only [map_one] using
        foxAlgebraicStagePowerSourceGroupAlgebraMap_single_apply
          (X := X) N hnm
          (1 : FreeGroup X ⧸
            foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) a
    calc
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N m₀ i (a • x))
        =
          foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
            (a • foxAlgebraicStageGroupAlgebraDerivative (X := X) N m₀ i x) := by
            rw [LinearMap.map_smul]
      _ =
          (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) •
            foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
              (foxAlgebraicStageGroupAlgebraDerivative (X := X) N m₀ i x) := by
            simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
                RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, htargetScalar]
      _ =
          (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) •
            foxAlgebraicStageGroupAlgebraDerivative (X := X) N n₀ i
              (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
            rw [hx]
      _ =
          foxAlgebraicStageGroupAlgebraDerivative (X := X) N n₀ i
            ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) •
              foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
            rw [LinearMap.map_smul]
      _ =
          foxAlgebraicStageGroupAlgebraDerivative (X := X) N n₀ i
            (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm (a • x)) := by
            congr 1
            simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
                RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, hsourceScalar]



end

end FoxDifferential
