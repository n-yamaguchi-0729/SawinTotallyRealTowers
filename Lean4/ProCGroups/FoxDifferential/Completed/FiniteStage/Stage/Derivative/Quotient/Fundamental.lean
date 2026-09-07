import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Boundary
import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Quotient.Basic

set_option autoImplicit false

/-!
# Fox differential: stage — derivative — quotient — fundamental

The principal declarations in this module are:

- `foxAlgebraicStageQuotientDerivative_fundamental_formula`
  Finite-stage Fox fundamental formula on the finite source quotient.
- `foxAlgebraicStageFoxBoundary_quotientDerivativeVector`
  Boundary-map form of the finite-stage Fox fundamental formula on the finite source quotient.
- `foxAlgebraicStageFoxBoundary_quotient_of_crossedHom`
  Any quotient-level scalar crossed homomorphism with standard generator values satisfies the Fox
  boundary formula.
- `foxAlgebraicStageQuotientDerivative_fundamental_formula_of_crossedHom`
  The quotient Fox fundamental formula for a scalar crossed homomorphism with standard generator
  values.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- Finite-stage Fox fundamental formula on the finite source quotient. -/
theorem foxAlgebraicStageQuotientDerivative_fundamental_formula
    [Fintype X]
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n q - 1 =
      ∑ i : X,
        foxAlgebraicStageQuotientDerivative (X := X) N n i q *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  rcases QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [foxAlgebraicStageQuotientCoefficient_mk]
  simp_rw [foxAlgebraicStageQuotientDerivative_mk]
  exact foxAlgebraicStageDerivative_fundamental_formula (X := X) N n w

/-- Boundary-map form of the finite-stage Fox fundamental formula on the finite source quotient. -/
theorem foxAlgebraicStageFoxBoundary_quotientDerivativeVector
    [Fintype X]
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageFoxBoundary (X := X) N n
        (foxAlgebraicStageQuotientDerivativeVector (X := X) N n q) =
      foxAlgebraicStageQuotientCoefficient (X := X) N n q - 1 := by
  rw [foxAlgebraicStageFoxBoundary_apply]
  simpa [foxAlgebraicStageQuotientDerivative] using
    (foxAlgebraicStageQuotientDerivative_fundamental_formula (X := X) N n q).symm

/--
Any quotient-level scalar crossed homomorphism with standard generator values satisfies the Fox
boundary formula.
-/
theorem foxAlgebraicStageFoxBoundary_quotient_of_crossedHom
    [Fintype X]
    (delta : ScalarCrossedHom
      (foxAlgebraicStageQuotientCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n))
    (hbasis :
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n))
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageFoxBoundary (X := X) N n (delta q) =
      foxAlgebraicStageQuotientCoefficient (X := X) N n q - 1 := by
  have hdelta_eq :
      delta = foxAlgebraicStageQuotientDerivativeVector (X := X) N n :=
    foxAlgebraicStageQuotientDerivativeVector_unique (X := X) N n delta hbasis
  rw [hdelta_eq]
  exact foxAlgebraicStageFoxBoundary_quotientDerivativeVector (X := X) N n q

/--
The quotient Fox fundamental formula for a scalar crossed homomorphism with standard generator
values.
-/
theorem foxAlgebraicStageQuotientDerivative_fundamental_formula_of_crossedHom
    [Fintype X]
    (delta : ScalarCrossedHom
      (foxAlgebraicStageQuotientCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n))
    (hbasis :
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n))
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n q - 1 =
      ∑ i : X,
        delta q i *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N)
            (QuotientGroup.mk' N (FreeGroup.of i)) - 1) := by
  simpa [foxAlgebraicStageFoxBoundary_apply] using
    (foxAlgebraicStageFoxBoundary_quotient_of_crossedHom
      (X := X) N n delta hbasis q).symm



end

end FoxDifferential
