import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Boundary
import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Relators
import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules
import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Fundamental

set_option autoImplicit false

/-!
# Fox differential: finite stage — stage — fundamental — derivative

The principal declarations in this module are:

- `foxAlgebraicStageGroupAlgebraDerivative`
  Linear extension of a descended finite-stage Fox derivative coordinate to the source group
  algebra.
- `foxAlgebraicStageGroupAlgebraDerivative_of_quotient`
  Evaluation of the finite-stage group-algebra derivative on a quotient basis element.
- `foxAlgebraicStageGroupAlgebraDerivative_of`
  Evaluation of the finite-stage group-algebra derivative on a represented word.
- `foxAlgebraicStageGroupAlgebraDerivative_one`
  The finite-stage group-algebra derivative sends the unit to zero.
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
Linear extension of a descended finite-stage Fox derivative coordinate to the source group
algebra.
-/
def foxAlgebraicStageGroupAlgebraDerivative (i : X) :
    MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) →ₗ[
      ModNCompletedCoeff n]
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  (Finsupp.linearCombination (ModNCompletedCoeff n)
    (foxAlgebraicStageQuotientDerivative (X := X) N n i)).comp
      (MonoidAlgebra.coeffLinearEquiv (ModNCompletedCoeff n)).toLinearMap

/-- Evaluation of the finite-stage group-algebra derivative on a quotient basis element. -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivative_of_quotient
    (i : X)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      foxAlgebraicStageQuotientDerivative (X := X) N n i q := by
  change
      (Finsupp.linearCombination (ModNCompletedCoeff n)
        (foxAlgebraicStageQuotientDerivative (X := X) N n i))
          (Finsupp.single q (1 : ModNCompletedCoeff n)) =
        foxAlgebraicStageQuotientDerivative (X := X) N n i q
  rw [Finsupp.linearCombination_single, one_smul]

/-- Evaluation of the finite-stage group-algebra derivative on a represented word. -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivative_of
    (i : X) (w : FreeGroup X) :
    foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w)) =
      foxAlgebraicStageDerivative (X := X) N n i w := by
  rw [foxAlgebraicStageGroupAlgebraDerivative_of_quotient,
    foxAlgebraicStageQuotientDerivative_mk]

/-- The finite-stage group-algebra derivative sends the unit to zero. -/
@[simp]
theorem foxAlgebraicStageGroupAlgebraDerivative_one (i : X) :
    foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
        (1 : MonoidAlgebra (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)) = 0 := by
  change foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (1 : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)) = 0
  rw [foxAlgebraicStageGroupAlgebraDerivative_of_quotient]
  change foxAlgebraicStageDerivative (X := X) N n i (1 : FreeGroup X) = 0
  simp only [foxAlgebraicStageDerivative_one]

/-- Product rule for the finite-stage group-algebra derivative on quotient basis elements. -/
theorem foxAlgebraicStageGroupAlgebraDerivative_of_quotient_mul
    (i : X)
    (q r : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (q * r)) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) +
        foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
          foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) r) := by
  rcases QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with
    ⟨u, rfl⟩
  rcases QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) r with
    ⟨v, rfl⟩
  change foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
      (MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) (u * v))) =
    _
  rw [foxAlgebraicStageGroupAlgebraDerivative_of,
    foxAlgebraicStageGroupAlgebraDerivative_of,
    foxAlgebraicStageGroupAlgebraDerivative_of,
    foxCommutatorPowerGroupAlgebraMap_of,
    foxAlgebraicStageDerivative_mul]

/--
Product rule for the finite-stage group-algebra derivative on arbitrary source group-algebra
elements.
-/
theorem foxAlgebraicStageGroupAlgebraDerivative_mul
    (i : X)
    (x y : MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i (x * y) =
      foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n y •
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x +
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x *
        foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i y := by
  classical
  let Source :=
    MonoidAlgebra (ModNCompletedCoeff n)
      (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
  let Target := foxAlgebraicStageTargetGroupAlgebra (X := X) N n
  let D : Source →ₗ[ModNCompletedCoeff n] Target :=
    foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
  let φ : Source →+* Target :=
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
  let ε : Source →ₐ[ModNCompletedCoeff n] ModNCompletedCoeff n :=
    foxCommutatorPowerSourceGroupAlgebraAugmentation (F := FreeGroup X) N n
  have h_right_basis
      (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
      (x : Source) :
      D (x * MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
        D x +
          φ x * D (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) := by
    let P := fun z : Source =>
      D (z * MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
        D z +
          φ z * D (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
    change P x
    refine MonoidAlgebra.induction_on (motive := P) x ?_ ?_ ?_
    · intro q'
      dsimp [P]
      have hprod :
          MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q' *
              MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q =
            MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (q' * q) :=
        (map_mul
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n))
          q' q).symm
      rw [hprod]
      have hbasis :=
        foxAlgebraicStageGroupAlgebraDerivative_of_quotient_mul
          (X := X) (N := N) (n := n) i q' q
      change
          D (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (q' * q)) =
            D (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') +
              φ (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q') *
                D (MonoidAlgebra.of (ModNCompletedCoeff n)
                  (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
        at hbasis
      exact hbasis
    · intro z w hz hw
      dsimp [P] at hz hw ⊢
      rw [add_mul, map_add, hz, hw, map_add, map_add, add_mul]
      abel
    · intro a z hz
      dsimp [P] at hz ⊢
      have hφ_smul :
          φ (a • z) = a • φ z := by
        dsimp [φ, foxCommutatorPowerGroupAlgebraMap]
        change
          MonoidAlgebra.mapDomain
              (foxCommutatorPowerQuotientMapToNormalQuotient
                (F := FreeGroup X) N n)
              (a • z) =
            a •
              MonoidAlgebra.mapDomain
                (foxCommutatorPowerQuotientMapToNormalQuotient
                  (F := FreeGroup X) N n)
                z
        exact MonoidAlgebra.mapDomain_smul _ _ _
      rw [smul_mul_assoc, map_smul, hz, map_smul, hφ_smul]
      simp only [smul_add, Algebra.smul_mul_assoc]
  change
    D (x * (y : Source)) =
      ε (y : Source) • D x + φ x * D (y : Source)
  let P := fun z : Source =>
    D (x * z) = ε z • D x + φ x * D z
  change P y
  refine MonoidAlgebra.induction_on (motive := P) y ?_ ?_ ?_
  · intro q
    dsimp [P]
    have hε :=
      foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient
        (F := FreeGroup X) N n q
    change
        ε (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      1 at hε
    rw [hε, one_smul]
    exact h_right_basis q x
  · intro z w hz hw
    dsimp [P] at hz hw ⊢
    rw [mul_add, map_add, hz, hw, map_add, map_add, left_distrib, add_smul]
    abel
  · intro a z hz
    dsimp [P] at hz ⊢
    rw [mul_smul_comm, map_smul, hz, map_smul, map_smul]
    simp only [smul_add, smul_smul, Algebra.mul_smul_comm, smul_eq_mul]



end

end FoxDifferential
