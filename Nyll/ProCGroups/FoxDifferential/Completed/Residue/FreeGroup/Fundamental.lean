/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Residue.FreeGroup.Boundary

/-!
# Fox differential: completed — residue — free group — fundamental

The principal declarations in this module are:

- `residueFreeGroupFoxBoundary_derivativeVector`
  Boundary-map form of the residue Fox fundamental formula.
- `residueFreeGroupFoxBoundary_of_crossedHom`
  Any residue crossed homomorphism with the standard basis values satisfies the residue Fox boundary
  formula.
- `residueFreeGroupFoxDerivative_fundamental_formula_of_crossedHom`
  The residue Fox-Euler sum computed from a crossed homomorphism with standard basis values is
  \([\psi(w)]-1\).
- `residueFreeGroupFoxDerivative_euler_formula_of_crossedHom`
  The explicit \([\psi(w)]-1\) form of the residue Fox-Euler formula for a crossed homomorphism.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v


variable {X : Type u} {H : Type v} [Group H] [DecidableEq X]

section FiniteBasis

variable [Fintype X]

/-- Boundary-map form of the residue Fox fundamental formula. -/
theorem residueFreeGroupFoxBoundary_derivativeVector
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueFreeGroupFoxBoundary n ψ
        (residueFreeGroupFoxDerivativeVector n ψ w) =
      residueGroupRingBoundary n ψ w := by
  let beta : ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueGroupRing n H) :=
    (residueFreeGroupFoxDerivativeVector n ψ).mapLinear
      (residueFreeGroupFoxBoundary n ψ)
  have hbasis :
      ∀ x : X, beta (FreeGroup.of x) =
        residueGroupRingBoundary n ψ (FreeGroup.of x) := by
    intro x
    simp only [beta, ScalarCrossedHom.mapLinear_apply,
      residueFreeGroupFoxDerivativeVector_of, residueFreeGroupFoxBoundary_single]
  have hbeta_eq :
      beta =
        freeCrossedHomWithCoeff
          (A := ResidueGroupRing n H)
          (residueGroupRingScalar n ψ)
          (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ResidueGroupRing n H)
      (residueGroupRingScalar n ψ)
      (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x)) beta hbasis
  have hboundary_eq :
      residueGroupRingBoundary n ψ =
        freeCrossedHomWithCoeff
          (A := ResidueGroupRing n H)
          (residueGroupRingScalar n ψ)
          (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x)) := by
    exact freeCrossedHomWithCoeff_unique
      (A := ResidueGroupRing n H)
      (residueGroupRingScalar n ψ)
      (fun x => residueGroupRingBoundary n ψ (FreeGroup.of x))
      (residueGroupRingBoundary n ψ) (by intro x; rfl)
  exact congrArg
    (fun d : ScalarCrossedHom (residueGroupRingScalar n ψ) (ResidueGroupRing n H) => d w)
    (hbeta_eq.trans hboundary_eq.symm)

/--
Any residue crossed homomorphism with the standard basis values satisfies the residue Fox
boundary formula.
-/
theorem residueFreeGroupFoxBoundary_of_crossedHom
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (residueGroupRingScalar n ψ)
      (ResidueFreeFoxCoordinates n H X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H))
    (w : FreeGroup X) :
    residueFreeGroupFoxBoundary n ψ (delta w) =
      residueGroupRingBoundary n ψ w := by
  have hdelta_eq :
      delta = residueFreeGroupFoxDerivativeVector n ψ :=
    residueFreeGroupFoxDerivativeVector_unique n ψ delta hbasis
  rw [hdelta_eq]
  exact residueFreeGroupFoxBoundary_derivativeVector n ψ w

/--
The residue Fox-Euler sum computed from a crossed homomorphism with standard basis values is
\([\psi(w)]-1\).
-/
theorem residueFreeGroupFoxDerivative_fundamental_formula_of_crossedHom
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (residueGroupRingScalar n ψ)
      (ResidueFreeFoxCoordinates n H X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H))
    (w : FreeGroup X) :
    residueGroupRingBoundary n ψ w =
      ∑ i : X,
        delta w i *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  simpa [residueFreeGroupFoxBoundary_apply] using
    (residueFreeGroupFoxBoundary_of_crossedHom n ψ delta hbasis w).symm

/--
The explicit \([\psi(w)]-1\) form of the residue Fox-Euler formula for a crossed homomorphism.
-/
theorem residueFreeGroupFoxDerivative_euler_formula_of_crossedHom
    (n : ℕ) (ψ : FreeGroup X →* H)
    (delta : ScalarCrossedHom (residueGroupRingScalar n ψ)
      (ResidueFreeFoxCoordinates n H X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) =
        Pi.single x (1 : ResidueGroupRing n H))
    (w : FreeGroup X) :
    (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ w) : ResidueGroupRing n H) - 1 =
      ∑ i : X,
        delta w i *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  have h := residueFreeGroupFoxDerivative_fundamental_formula_of_crossedHom
    n ψ delta hbasis w
  change (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ w) :
    ResidueGroupRing n H) - 1 = _ at h
  exact h

/--
The residue Fox fundamental formula, also known as the residue Fox-Euler formula: \([\psi(w)]-1
= \sum_i (\partial w/\partial x_i)([\psi(x_i)]-1)\).
-/
theorem residueFreeGroupFoxDerivative_fundamental_formula
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    residueGroupRingBoundary n ψ w =
      ∑ i : X,
        residueFreeGroupFoxDerivative n ψ i w *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  simpa [residueFreeGroupFoxBoundary_apply, residueFreeGroupFoxDerivative] using
    (residueFreeGroupFoxBoundary_derivativeVector n ψ w).symm

/-- The explicit \([\psi(w)]-1\) form of the residue Fox-Euler formula. -/
theorem residueFreeGroupFoxDerivative_euler_formula
    (n : ℕ) (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ w) : ResidueGroupRing n H) - 1 =
      ∑ i : X,
        residueFreeGroupFoxDerivative n ψ i w *
          (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ (FreeGroup.of i)) - 1) := by
  have h := residueFreeGroupFoxDerivative_fundamental_formula n ψ w
  change (MonoidAlgebra.of (ModNCompletedCoeff n) H (ψ w) :
    ResidueGroupRing n H) - 1 = _ at h
  exact h

end FiniteBasis


end

end FoxDifferential
