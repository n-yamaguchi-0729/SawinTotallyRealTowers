import ProCGroups.FoxDifferential.Completed.FiniteStage.TargetMap

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — bifiltered — transition

The principal declarations in this module are:

- `foxAlgebraicStageBifilteredTargetGroupAlgebraMap`
  Combined coefficient/target transition on finite target group algebras.
- `foxAlgebraicStageBifilteredCoordinateVectorMap`
  Combined coefficient/target transition on finite Fox coordinate vectors.
- `foxAlgebraicStageBifilteredTargetGroupAlgebraMap_apply`
  The bifiltered finite-stage target group-algebra map is evaluated by reducing coefficients and
  mapping the group coordinate to the target quotient.
- `foxAlgebraicStageBifilteredTargetGroupAlgebraMap_of`
  Evaluation of the bifiltered target-group-algebra transition on a represented word.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)

/-- Combined coefficient/target transition on finite target group algebras. -/
def foxAlgebraicStageBifilteredTargetGroupAlgebraMap :
    foxAlgebraicStageTargetGroupAlgebra (X := X) N m →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) M n :=
  (foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n).comp
    (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/--
The bifiltered finite-stage target group-algebra map is evaluated by reducing coefficients and
mapping the group coordinate to the target quotient.
-/
@[simp]
theorem foxAlgebraicStageBifilteredTargetGroupAlgebraMap_apply
    (x : foxAlgebraicStageTargetGroupAlgebra (X := X) N m) :
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm x =
      foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm x) :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- Evaluation of the bifiltered target-group-algebra transition on a represented word. -/
@[simp]
theorem foxAlgebraicStageBifilteredTargetGroupAlgebraMap_of
    (w : FreeGroup X) :
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m)
          (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) M) (QuotientGroup.mk' M w) := by
  rw [foxAlgebraicStageBifilteredTargetGroupAlgebraMap_apply]
  rw [foxAlgebraicStageTargetGroupAlgebraCoeffMap_of]
  rw [foxAlgebraicStageTargetGroupAlgebraMap_of]

/-- Combined coefficient/target transition on finite Fox coordinate vectors. -/
def foxAlgebraicStageBifilteredCoordinateVectorMap
    (v : foxAlgebraicStageCoordinateVector (X := X) N m) :
    foxAlgebraicStageCoordinateVector (X := X) M n :=
  fun i : X => foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm (v i)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- Combined coefficient/target transition commutes with the finite-stage Fox boundary. -/
theorem foxAlgebraicStageFoxBoundary_bifilteredMap
    [Fintype X]
    (v : foxAlgebraicStageCoordinateVector (X := X) N m) :
    foxAlgebraicStageFoxBoundary (X := X) M n
        (foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm v) =
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (foxAlgebraicStageFoxBoundary (X := X) N m v) := by
  calc
    foxAlgebraicStageFoxBoundary (X := X) M n
        (foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm v) =
      foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageFoxBoundary (X := X) N n
          (fun i : X => foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i))) := by
        exact foxAlgebraicStageFoxBoundary_targetMap (X := X) hNM n
          (fun i : X => foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm (v i))
    _ = foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (foxAlgebraicStageFoxBoundary (X := X) N m v) := by
        rw [← foxAlgebraicStageFoxBoundary_coeffMap (X := X) N hnm v]
        rfl

/-- Combined coefficient/target transition on finite-stage semidirect Fox targets. -/
def foxAlgebraicStageBifilteredSemidirectMap :
    FoxAlgebraicStageSemidirect (X := X) N m →*
      FoxAlgebraicStageSemidirect (X := X) M n :=
  (foxAlgebraicStageSemidirectMap (X := X) hNM n).comp
    (foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/--
The left coordinate of the finite-stage semidirect point is the specified derivative component.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectMap_left
    (y : FoxAlgebraicStageSemidirect (X := X) N m) :
    (foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm y).left =
      foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) hNM hnm y.left :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/--
The right coordinate of the finite-stage semidirect point is the corresponding quotient
component.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectMap_right
    (y : FoxAlgebraicStageSemidirect (X := X) N m) :
    (foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm y).right =
      foxAlgebraicStageTargetQuotientMap (X := X) hNM y.right :=
  rfl

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The combined transition sends kernel-word points to kernel-word points. -/
theorem foxAlgebraicStageBifilteredSemidirectMap_kernelWordPoint
    (w : FreeGroup X) :
    foxAlgebraicStageBifilteredSemidirectMap (X := X) hNM hnm
        (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N m w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) M n w := by
  change foxAlgebraicStageSemidirectMap (X := X) hNM n
      (foxAlgebraicStageSemidirectCoeffMap (X := X) N hnm
        (foxAlgebraicStageSemidirectKernelWordPoint (X := X) N m w)) =
    foxAlgebraicStageSemidirectKernelWordPoint (X := X) M n w
  rw [foxAlgebraicStageSemidirectCoeffMap_kernelWordPoint]
  exact foxAlgebraicStageSemidirectMap_kernelWordPoint (X := X) hNM n w

end

end FoxDifferential
