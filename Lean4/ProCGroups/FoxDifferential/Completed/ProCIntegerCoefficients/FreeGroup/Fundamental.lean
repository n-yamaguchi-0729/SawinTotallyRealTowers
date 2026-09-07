import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.FreeGroup.Coordinates

set_option autoImplicit false

/-!
# Fox differential: completed — \(\mathbb{Z}_C\) coefficients — free group — fundamental

The principal declarations in this module are:

- `zcFreeGroupFoxBoundary_derivativeVector`
  The boundary-map form of the completed Fox fundamental formula.
- `zcFreeGroupFoxBoundary_of_crossedHom`
  Conditional completed Fox boundary formula. Any completed crossed differential on a free group
  with the standard basis values satisfies the completed Fox boundary formula.
- `zcFreeGroupFoxDerivative_fundamental_formula_of_crossedHom`
  Conditional completed Fox fundamental formula. The finite Fox-Euler sum computed from any
  completed crossed differential with standard basis values is \([\psi(w)]-1\).
- `zcFreeGroupFoxDerivative_euler_formula_of_crossedHom`
  The explicit \([\psi(w)]-1\) form of the conditional completed Fox-Euler formula.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable (C : ProCGroups.FiniteGroupClass.{v})
variable {X : Type u} [DecidableEq X]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

section FiniteBasis

variable [Fintype X]

/-- The boundary-map form of the completed Fox fundamental formula. -/
theorem zcFreeGroupFoxBoundary_derivativeVector
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcFreeGroupFoxBoundary C ψ (zcFreeGroupFoxDerivativeVector C ψ w) =
      zcCompletedGroupAlgebraBoundary C ψ w := by
  let beta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedGroupAlgebra C H) :=
    (zcFreeGroupFoxDerivativeVector C ψ).mapLinear
      (zcFreeGroupFoxBoundary C ψ)
  have hbasis :
      ∀ x : X, beta (FreeGroup.of x) =
        zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x) := by
    intro x
    change zcFreeGroupFoxBoundary C ψ
        (zcFreeGroupFoxDerivativeVector C ψ (FreeGroup.of x)) =
      zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x)
    rw [zcFreeGroupFoxDerivativeVector_of, zcFreeGroupFoxBoundary_single]
  have hbeta_eq :
      beta =
        freeCrossedHomWithCoeff
          (A := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraScalar C ψ)
          (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)
      (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x))
      beta hbasis
  have hboundary_eq :
      zcCompletedGroupAlgebraBoundary C ψ =
        freeCrossedHomWithCoeff
          (A := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraScalar C ψ)
          (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraScalar C ψ)
      (fun x => zcCompletedGroupAlgebraBoundary C ψ (FreeGroup.of x))
      (zcCompletedGroupAlgebraBoundary C ψ) (by intro x; rfl)
  exact congrArg
    (fun d : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedGroupAlgebra C H) => d w)
    (hbeta_eq.trans hboundary_eq.symm)

/--
Conditional completed Fox boundary formula. Any completed crossed differential on a free group
with the standard basis values satisfies the completed Fox boundary formula.
-/
theorem zcFreeGroupFoxBoundary_of_crossedHom
    (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcFreeGroupFoxBoundary C ψ (delta w) =
      zcCompletedGroupAlgebraBoundary C ψ w := by
  have hdelta_eq :
      delta = zcFreeGroupFoxDerivativeVector C ψ :=
    zcFreeGroupFoxDerivativeVector_unique C ψ delta hbasis
  rw [hdelta_eq]
  exact zcFreeGroupFoxBoundary_derivativeVector C ψ w

/--
Conditional completed Fox fundamental formula. The finite Fox-Euler sum computed from any
completed crossed differential with standard basis values is \([\psi(w)]-1\).
-/
theorem zcFreeGroupFoxDerivative_fundamental_formula_of_crossedHom
    (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcCompletedGroupAlgebraBoundary C ψ w =
      ∑ i : X,
        delta w i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  simpa [zcFreeGroupFoxBoundary_apply] using
    (zcFreeGroupFoxBoundary_of_crossedHom C ψ delta hbasis w).symm

/-- The explicit \([\psi(w)]-1\) form of the conditional completed Fox-Euler formula. -/
theorem zcFreeGroupFoxDerivative_euler_formula_of_crossedHom
    (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcGroupLike C H (ψ w) - 1 =
      ∑ i : X,
        delta w i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  have h := zcFreeGroupFoxDerivative_fundamental_formula_of_crossedHom
    C ψ delta hbasis w
  change zcGroupLike C H (ψ w) - 1 = _ at h
  exact h

/--
The completed Fox fundamental formula, also known as the completed Fox-Euler formula:
\([\psi(w)]-1 = \sum_i (\partial w/\partial x_i)([\psi(x_i)]-1)\).
-/
theorem zcFreeGroupFoxDerivative_fundamental_formula
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcCompletedGroupAlgebraBoundary C ψ w =
      ∑ i : X,
        zcFreeGroupFoxDerivative C ψ i w *
          (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  simpa [zcFreeGroupFoxBoundary_apply, zcFreeGroupFoxDerivative] using
    (zcFreeGroupFoxBoundary_derivativeVector C ψ w).symm

/-- The explicit \([\psi(w)]-1\) form of the completed Fox-Euler formula. -/
theorem zcFreeGroupFoxDerivative_euler_formula
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcGroupLike C H (ψ w) - 1 =
      ∑ i : X,
        zcFreeGroupFoxDerivative C ψ i w *
          (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  have h := zcFreeGroupFoxDerivative_fundamental_formula C ψ w
  change zcGroupLike C H (ψ w) - 1 = _ at h
  exact h


end FiniteBasis


end

end FoxDifferential
