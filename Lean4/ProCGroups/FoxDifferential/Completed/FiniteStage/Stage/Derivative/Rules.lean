import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Lift
import ProCGroups.FoxDifferential.Completed.Residue.FreeGroup.Coordinates

set_option autoImplicit false

/-!
# Fox differential: finite stage — stage — derivative — rules

The principal declarations in this module are:

- `foxAlgebraicStageDerivativeVectorCrossedHom`
  The finite-stage Fox derivative vector, bundled with its scalar Fox--Leibniz law.
- `foxAlgebraicStageDerivative_one`
  The finite-stage derivative sends the identity word to zero componentwise.
- `foxAlgebraicStageDerivativeVector_of`
  The finite-stage derivative vector sends a free generator to the corresponding coordinate basis
  vector.
- `foxAlgebraicStageDerivative_mul`
  The finite-stage Fox product rule holds componentwise.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite-stage Fox derivative vector, bundled with its scalar Fox--Leibniz law. -/
def foxAlgebraicStageDerivativeVectorCrossedHom :
    ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n) where
  toFun w := (foxAlgebraicStageLift (X := X) N n w).left
  map_mul' := by
    intro u v
    simp only [scalarCrossedAction_apply, map_mul,
      FoxAlgebraicStageSemidirect.mul_left, foxAlgebraicStageLift_right,
      foxAlgebraicStageCoefficient_apply, QuotientGroup.mk'_apply,
      MonoidAlgebra.of_apply]

/-- The finite-stage derivative sends the identity word to zero componentwise. -/
@[simp]
theorem foxAlgebraicStageDerivative_one (i : X) :
    foxAlgebraicStageDerivative (X := X) N n i (1 : FreeGroup X) = 0 := by
  change foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n 1 i = 0
  rw [ScalarCrossedHom.map_one]
  rfl

/--
The finite-stage derivative vector sends a free generator to the corresponding coordinate basis
vector.
-/
@[simp]
theorem foxAlgebraicStageDerivativeVector_of (x : X) :
    foxAlgebraicStageDerivativeVector (X := X) N n (FreeGroup.of x) =
      Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
  simp only [foxAlgebraicStageDerivativeVector, foxAlgebraicStageLift, QuotientGroup.mk'_apply,
  FreeGroup.lift_apply_of]

/-- The finite-stage Fox product rule holds componentwise. -/
theorem foxAlgebraicStageDerivative_mul (i : X) (u v : FreeGroup X) :
    foxAlgebraicStageDerivative (X := X) N n i (u * v) =
      foxAlgebraicStageDerivative (X := X) N n i u +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N u)) *
          foxAlgebraicStageDerivative (X := X) N n i v := by
  have h := congrFun
    (ScalarCrossedHom.map_mul
      (foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n) u v) i
  change
    foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n (u * v) i =
      (foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n u +
        foxAlgebraicStageCoefficient (X := X) N n u •
          foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n v) i
  exact h

/--
The bundled finite-stage Fox derivative vector is uniquely determined by its values on free
generators.
-/
theorem foxAlgebraicStageDerivativeVector_unique
    (delta : ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)) :
    delta = foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n := by
  have hdelta_free := freeCrossedHomWithCoeff_unique
    (A := foxAlgebraicStageCoordinateVector (X := X) N n)
    (foxAlgebraicStageCoefficient (X := X) N n)
    (fun x => Pi.single x
      (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n))
    delta hbasis
  have hstage_free := freeCrossedHomWithCoeff_unique
    (A := foxAlgebraicStageCoordinateVector (X := X) N n)
    (foxAlgebraicStageCoefficient (X := X) N n)
    (fun x => Pi.single x
      (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n))
    (foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n)
    (by
      intro x
      change foxAlgebraicStageDerivativeVector (X := X) N n (FreeGroup.of x) =
        Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
      exact foxAlgebraicStageDerivativeVector_of (X := X) N n x)
  exact hdelta_free.trans hstage_free.symm

/--
The finite-stage derivative is exactly the residue free Fox derivative for the quotient map
\(\mathrm{FreeGroup}(X) \to F/N\).
-/
theorem foxAlgebraicStageDerivativeVector_eq_residueFreeGroupFoxDerivativeVector :
    foxAlgebraicStageDerivativeVector (X := X) N n =
      residueFreeGroupFoxDerivativeVector n (QuotientGroup.mk' N) := by
  have h := residueFreeGroupFoxDerivativeVector_unique n (QuotientGroup.mk' N)
    (foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n)
    (by
      intro x
      change foxAlgebraicStageDerivativeVector (X := X) N n (FreeGroup.of x) =
        Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
      exact foxAlgebraicStageDerivativeVector_of (X := X) N n x)
  exact congrArg CrossedHom.toFun h

/--
For a finite free basis, finite-stage derivative-vector zero is the same as zero of the residue
universal differential.
-/
theorem foxAlgebraicStageDerivativeVector_eq_zero_iff_residueUniversalDifferential_eq_zero
    [Finite X]
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ} {w : FreeGroup X} :
    foxAlgebraicStageDerivativeVector (X := X) N n w = 0 ↔
      residueUniversalDifferential n (QuotientGroup.mk' N) w = 0 := by
  classical
  let : Fintype X := Fintype.ofFinite X
  rw [foxAlgebraicStageDerivativeVector_eq_residueFreeGroupFoxDerivativeVector]
  constructor
  · intro h
    rw [← residueFreeFoxCoordinatesLinearMap_derivativeVector
      n (QuotientGroup.mk' N) w, h, map_zero]
  · intro h
    rw [← residueDifferentialToFreeFoxCoordinates_universal
      n (QuotientGroup.mk' N) w, h, map_zero]

end

end FoxDifferential
