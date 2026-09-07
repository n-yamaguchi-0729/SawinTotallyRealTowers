import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Fundamental.Derivative

set_option autoImplicit false

/-!
# Fox differential: finite stage — stage — fundamental — formula

The principal declarations in this module are:

- `foxAlgebraicStageGroupAlgebraDerivative_of_quotient_fundamental_formula`
  Finite-stage Fox fundamental formula on a source quotient basis element after mapping to the
  target group algebra.
- `foxAlgebraicStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula_algHom`
  Algebra-homomorphism form of the finite-stage Fox fundamental formula on the source group algebra.
- `foxAlgebraicStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula`
  Ring-hom form of the finite-stage Fox fundamental formula on the source group algebra.
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
Finite-stage Fox fundamental formula on a source quotient basis element after mapping to the
target group algebra.
-/
theorem foxAlgebraicStageGroupAlgebraDerivative_of_quotient_fundamental_formula
    [Fintype X]
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) - 1 =
      ∑ i : X,
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rcases QuotientGroup.mk'_surjective
    (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [foxCommutatorPowerGroupAlgebraMap_of]
  simp_rw [foxAlgebraicStageGroupAlgebraDerivative_of]
  exact foxAlgebraicStageDerivative_fundamental_formula (X := X) (N := N) (n := n) w

/--
Algebra-homomorphism form of the finite-stage Fox fundamental formula on the source group
algebra.
-/
theorem foxAlgebraicStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula_algHom
    [Fintype X]
    (x : MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n x -
        algebraMap (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) =
      ∑ i : X,
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  classical
  let P := fun y :
      MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) =>
    foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n y -
        algebraMap (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n y) =
      ∑ i : X,
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i y *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1)
  change P x
  refine MonoidAlgebra.induction_on (motive := P) x ?_ ?_ ?_
  · intro q
    dsimp [P]
    rw [foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient]
    simpa only [MonoidAlgebra.one_def, QuotientGroup.mk'_apply] using
      foxAlgebraicStageGroupAlgebraDerivative_of_quotient_fundamental_formula
        (X := X) (N := N) (n := n) q
  · intro x y hx hy
    dsimp [P] at hx hy ⊢
    calc
      foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n (x + y) -
          algebraMap (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (x + y)) =
          (foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n x -
              algebraMap (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
                (foxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n x)) +
            (foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n y -
              algebraMap (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
                (foxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n y)) := by
        rw [map_add, map_add, map_add]
        abel
      _ = (∑ i : X,
            foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) +
          (∑ i : X,
            foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i y *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) := by
        exact congrArg₂ (· + ·) hx hy
      _ = ∑ i : X,
            (foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x +
              foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i y) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_mul]
      _ = ∑ i : X,
            foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i (x + y) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_add]
  · intro a y hy
    dsimp [P] at hy ⊢
    calc
      foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n
            (a • y) -
          algebraMap (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (a • y)) =
          a •
            (foxCommutatorPowerGroupAlgebraAlgHom (F := FreeGroup X) N n y -
              algebraMap (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
                (foxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n y)) := by
        rw [map_smul, map_smul, smul_sub]
        simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self,
          RingHom.coe_id, id_eq]
      _ = a • (∑ i : X,
            foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
              y *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1)) := by
        exact congrArg (fun z => a • z) hy
      _ = ∑ i : X,
            foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
              (a • y) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (foxAlgebraicStageTargetQuotient (X := X) N)
                (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, smul_mul_assoc]

/-- Ring-hom form of the finite-stage Fox fundamental formula on the source group algebra. -/
theorem foxAlgebraicStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    [Fintype X]
    (x : MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x -
        algebraMap (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) =
      ∑ i : X,
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa using
    foxAlgebraicStageGroupAlgebraDerivative_groupAlgebra_fundamental_formula_algHom
      (X := X) (N := N) (n := n) x



end

end FoxDifferential
