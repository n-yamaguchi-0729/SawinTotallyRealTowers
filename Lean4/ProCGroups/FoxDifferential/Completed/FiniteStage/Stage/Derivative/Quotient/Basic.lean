import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Relators
import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Rules

set_option autoImplicit false

/-!
# Fox differential: stage — derivative — quotient — basic

The principal declarations in this module are:

- `foxAlgebraicStageQuotientLift`
  The finite-stage lift descended to the source quotient \(F/[N,N]N^n\).
- `foxAlgebraicStageQuotientCoefficient`
  Coefficient homomorphism for the finite-stage quotient crossed homomorphism.
- `foxAlgebraicStageQuotientLift_mk`
  Evaluation of the descended finite-stage lift on a representative.
- `foxAlgebraicStageQuotientLift_right`
  The right component of the descended finite-stage lift is the quotient map from \(F/[N,N]N^n\) to
  \(F/N\).
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- The finite-stage lift descended to the source quotient \(F/[N,N]N^n\). -/
def foxAlgebraicStageQuotientLift :
    FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n →*
      FoxAlgebraicStageSemidirect (X := X) N n :=
  QuotientGroup.lift
    (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    (foxAlgebraicStageLift (X := X) N n)
    (foxCommutatorPowerSubgroup_le_ker_foxAlgebraicStageLift
      (X := X) N n)

/-- Evaluation of the descended finite-stage lift on a representative. -/
@[simp]
theorem foxAlgebraicStageQuotientLift_mk (w : FreeGroup X) :
    foxAlgebraicStageQuotientLift (X := X) N n
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      foxAlgebraicStageLift (X := X) N n w := by
  rfl

/--
The right component of the descended finite-stage lift is the quotient map from \(F/[N,N]N^n\)
to \(F/N\).
-/
@[simp]
theorem foxAlgebraicStageQuotientLift_right
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    (foxAlgebraicStageQuotientLift (X := X) N n q).right =
      foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q := by
  rcases QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [foxAlgebraicStageQuotientLift_mk, foxAlgebraicStageLift_right,
    foxCommutatorPowerQuotientMapToNormalQuotient_mk]

/-- Coefficient homomorphism for the finite-stage quotient crossed homomorphism. -/
def foxAlgebraicStageQuotientCoefficient :
    (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) →*
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  (MonoidAlgebra.of (ModNCompletedCoeff n)
    (foxAlgebraicStageTargetQuotient (X := X) N)).comp
      (foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n)

/--
The finite-stage derivative vector descended to \(F/[N,N]N^n\), bundled with its scalar
Fox--Leibniz law.
-/
def foxAlgebraicStageQuotientDerivativeVector :
    ScalarCrossedHom
      (foxAlgebraicStageQuotientCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n) where
  toFun q := (foxAlgebraicStageQuotientLift (X := X) N n q).left
  map_mul' := by
    intro q r
    simp only [scalarCrossedAction_apply, map_mul,
      FoxAlgebraicStageSemidirect.mul_left,
      foxAlgebraicStageQuotientLift_right,
      foxAlgebraicStageQuotientCoefficient, MonoidHom.coe_comp,
      Function.comp_apply, MonoidAlgebra.of_apply]

/-- Evaluation of the descended derivative vector on a representative. -/
@[simp]
theorem foxAlgebraicStageQuotientDerivativeVector_mk (w : FreeGroup X) :
    foxAlgebraicStageQuotientDerivativeVector (X := X) N n
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      foxAlgebraicStageDerivativeVector (X := X) N n w := by
  rfl

/-- A coordinate of the descended finite-stage derivative on the source quotient. -/
def foxAlgebraicStageQuotientDerivative (i : X)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  foxAlgebraicStageQuotientDerivativeVector (X := X) N n q i

/-- Evaluation of a descended derivative coordinate on a representative. -/
@[simp]
theorem foxAlgebraicStageQuotientDerivative_mk (i : X) (w : FreeGroup X) :
    foxAlgebraicStageQuotientDerivative (X := X) N n i
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      foxAlgebraicStageDerivative (X := X) N n i w := by
  rfl

omit [DecidableEq X] in
/--
The finite Fox-stage quotient coefficient is evaluated by projecting the group coordinate and
reducing the coefficient.
-/
@[simp]
theorem foxAlgebraicStageQuotientCoefficient_apply
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n q =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (foxCommutatorPowerQuotientMapToNormalQuotient (F := FreeGroup X) N n q) :=
  rfl

omit [DecidableEq X] in
/--
The quotient coefficient homomorphism agrees with the free-group coefficient homomorphism on
representatives.
-/
@[simp]
theorem foxAlgebraicStageQuotientCoefficient_mk (w : FreeGroup X) :
    foxAlgebraicStageQuotientCoefficient (X := X) N n
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      foxAlgebraicStageCoefficient (X := X) N n w := by
  rfl

/-- The descended finite-stage derivative sends the identity word to zero componentwise. -/
@[simp]
theorem foxAlgebraicStageQuotientDerivative_one (i : X) :
    foxAlgebraicStageQuotientDerivative (X := X) N n i
        (1 : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) = 0 := by
  change foxAlgebraicStageQuotientDerivativeVector (X := X) N n 1 i = 0
  rw [ScalarCrossedHom.map_one]
  rfl

/-- Generator value for the descended finite-stage derivative vector. -/
@[simp]
theorem foxAlgebraicStageQuotientDerivativeVector_of (x : X) :
    foxAlgebraicStageQuotientDerivativeVector (X := X) N n
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) (FreeGroup.of x)) =
      Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
  rw [foxAlgebraicStageQuotientDerivativeVector_mk, foxAlgebraicStageDerivativeVector_of]

/-- At a generator, the descended finite-stage derivative has the corresponding component value. -/
@[simp]
theorem foxAlgebraicStageQuotientDerivative_of (i x : X) :
    foxAlgebraicStageQuotientDerivative (X := X) N n i
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) (FreeGroup.of x)) =
      (Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) :
        X → foxAlgebraicStageTargetGroupAlgebra (X := X) N n) i := by
  rw [foxAlgebraicStageQuotientDerivative, foxAlgebraicStageQuotientDerivativeVector_of]

/--
The bundled descended derivative vector is uniquely determined by its values on quotient
generators.
-/
theorem foxAlgebraicStageQuotientDerivativeVector_unique
    (delta : ScalarCrossedHom
      (foxAlgebraicStageQuotientCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n))
    (hbasis :
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)) :
    delta = foxAlgebraicStageQuotientDerivativeVector (X := X) N n := by
  let C : Subgroup (FreeGroup X) :=
    foxCommutatorPowerSubgroup (F := FreeGroup X) N n
  let deltaFree : ScalarCrossedHom
      (foxAlgebraicStageCoefficient (X := X) N n)
      (foxAlgebraicStageCoordinateVector (X := X) N n) :=
    { toFun w := delta (QuotientGroup.mk' C w)
      map_mul' := by
        intro u v
        simpa only [scalarCrossedAction_apply, map_mul, C,
          foxAlgebraicStageQuotientCoefficient_mk] using
          ScalarCrossedHom.map_mul delta
            (QuotientGroup.mk' C u) (QuotientGroup.mk' C v) }
  have hbasis_comp :
      ∀ x : X,
        deltaFree (FreeGroup.of x) =
          Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
    intro x
    change delta (QuotientGroup.mk' C (FreeGroup.of x)) =
      Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
    exact hbasis x
  have hfree :
      deltaFree = foxAlgebraicStageDerivativeVectorCrossedHom (X := X) N n :=
    foxAlgebraicStageDerivativeVector_unique (X := X) N n
      deltaFree hbasis_comp
  apply CrossedHom.ext
  intro q
  rcases QuotientGroup.mk'_surjective C q with ⟨w, rfl⟩
  have hw := congrArg (fun d => d w) hfree
  change delta (QuotientGroup.mk' C w) =
    foxAlgebraicStageDerivativeVector (X := X) N n w at hw
  change delta (QuotientGroup.mk' C w) =
    foxAlgebraicStageQuotientDerivativeVector (X := X) N n
      (QuotientGroup.mk' C w)
  rw [foxAlgebraicStageQuotientDerivativeVector_mk]
  exact hw

/--
Existence and uniqueness theorem for the descended finite-stage Fox derivative vector on the
finite source quotient.
-/
theorem existsUnique_foxAlgebraicStageQuotientDerivativeVector :
    ∃! delta : ScalarCrossedHom
        (foxAlgebraicStageQuotientCoefficient (X := X) N n)
        (foxAlgebraicStageCoordinateVector (X := X) N n),
      ∀ x : X,
        delta
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (FreeGroup.of x)) =
          Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
  refine ⟨foxAlgebraicStageQuotientDerivativeVector (X := X) N n, ?_, ?_⟩
  · exact foxAlgebraicStageQuotientDerivativeVector_of (X := X) N n
  · intro delta hdelta
    exact foxAlgebraicStageQuotientDerivativeVector_unique (X := X) N n
      delta hdelta



end

end FoxDifferential
