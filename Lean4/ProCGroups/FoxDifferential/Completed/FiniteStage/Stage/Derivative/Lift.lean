import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Semidirect

set_option autoImplicit false

/-!
# Fox differential: finite stage — stage — derivative — lift

The principal declarations in this module are:

- `foxAlgebraicStageLift`
  Semidirect-product lift defining the finite-stage Fox derivative.
- `foxAlgebraicStageDerivativeVector`
  Finite-stage Fox derivative vector of a free-group word.
- `foxAlgebraicStageLift_right`
  The right component of the finite-stage lift is the quotient class in \(F/N\).
- `foxAlgebraicStageCoefficient_apply`
  The finite Fox-stage coefficient map is evaluated by applying the selected coefficient projection.
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

/-- Semidirect-product lift defining the finite-stage Fox derivative. -/
def foxAlgebraicStageLift :
    FreeGroup X →* FoxAlgebraicStageSemidirect (X := X) N n :=
  FreeGroup.lift fun x =>
    { left := Pi.single x (1 : foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
      right := QuotientGroup.mk' N (FreeGroup.of x) }

/-- The right component of the finite-stage lift is the quotient class in \(F/N\). -/
@[simp]
theorem foxAlgebraicStageLift_right (w : FreeGroup X) :
    (foxAlgebraicStageLift (X := X) N n w).right =
      QuotientGroup.mk' N w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [foxAlgebraicStageLift, QuotientGroup.mk'_apply, map_one,
          FoxAlgebraicStageSemidirect.one_right]
  | of x =>
      simp only [foxAlgebraicStageLift, QuotientGroup.mk'_apply, FreeGroup.lift_apply_of]
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, FoxAlgebraicStageSemidirect.mul_right, hx, QuotientGroup.mk'_apply, hy]

/-- Finite-stage Fox derivative vector of a free-group word. -/
def foxAlgebraicStageDerivativeVector (w : FreeGroup X) :
    foxAlgebraicStageCoordinateVector (X := X) N n :=
  (foxAlgebraicStageLift (X := X) N n w).left

/-- A coordinate of the finite-stage Fox derivative vector. -/
def foxAlgebraicStageDerivative (i : X) (w : FreeGroup X) :
    foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  foxAlgebraicStageDerivativeVector (X := X) N n w i

/-- The coefficient map for the finite-stage Fox crossed differential. -/
def foxAlgebraicStageCoefficient :
    FreeGroup X →* foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  (MonoidAlgebra.of (ModNCompletedCoeff n)
    (foxAlgebraicStageTargetQuotient (X := X) N)).comp (QuotientGroup.mk' N)

omit [DecidableEq X] in
/--
The finite Fox-stage coefficient map is evaluated by applying the selected coefficient
projection.
-/
@[simp]
theorem foxAlgebraicStageCoefficient_apply (w : FreeGroup X) :
    foxAlgebraicStageCoefficient (X := X) N n w =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) :=
  rfl


end

end FoxDifferential
