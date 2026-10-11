/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Semidirect
import Nyll.ProCGroups.FoxDifferential.Discrete.DifferentialModule.Universal
import Nyll.ProCGroups.FoxDifferential.Common.FreeCrossedDifferential

/-!
# Fox differential: discrete — fox calculus — derivative

The principal declarations in this module are:

- `relativeFreeGroupFoxLift`
  The semidirect-product lift whose left component is the Fox derivative pushed forward by \(\psi\),
  and whose right component is \(\psi\) itself.
- `relativeFreeGroupFoxDerivative`
  The Fox derivative of a free-group word, with coefficients pushed forward to \(\mathbb{Z}[H]\) by
  \(\psi\).
- `relativeFreeGroupFoxLift_right`
  The right component of the relative Fox lift is the target homomorphism \(\psi\).
- `relativeFreeGroupFoxDerivative_one`
  The relative Fox derivative of the identity word is zero.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators commutatorElement

universe u v


variable {H : Type v} [Group H]
variable (X : Type u)

variable [DecidableEq X]
variable (ψ : FreeGroup X →* H)

/--
The semidirect-product lift whose left component is the Fox derivative pushed forward by
\(\psi\), and whose right component is \(\psi\) itself.
-/
def relativeFreeGroupFoxLift :
    FreeGroup X →* CrossedSemidirectProduct (RelativeFoxAction (H := H) X) :=
  FreeGroup.lift fun x =>
    { left := Multiplicative.ofAdd (Pi.single x (1 : GroupRing H))
      right := ψ (FreeGroup.of x) }

/--
The Fox derivative of a free-group word, with coefficients pushed forward to \(\mathbb{Z}[H]\)
by \(\psi\).
-/
def relativeFreeGroupFoxDerivative (w : FreeGroup X) :
    RelativeFreeFoxCoordinates (H := H) X :=
  Multiplicative.toAdd (relativeFreeGroupFoxLift (H := H) X ψ w).left

/-- The right component of the relative Fox lift is the target homomorphism \(\psi\). -/
@[simp]
theorem relativeFreeGroupFoxLift_right (w : FreeGroup X) :
    (relativeFreeGroupFoxLift (H := H) X ψ w).right = ψ w := by
  induction w using FreeGroup.induction_on with
  | one =>
      simp only [relativeFreeGroupFoxLift, map_one, SemidirectProduct.one_right]
  | of x =>
      simp only [relativeFreeGroupFoxLift, FreeGroup.lift_apply_of]
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, SemidirectProduct.mul_right, hx, hy]

/-- The relative Fox derivative of the identity word is zero. -/
@[simp]
theorem relativeFreeGroupFoxDerivative_one :
    relativeFreeGroupFoxDerivative (H := H) X ψ (1 : FreeGroup X) = 0 := by
  simp only [relativeFreeGroupFoxDerivative, relativeFreeGroupFoxLift, map_one,
    SemidirectProduct.one_left, toAdd_one]

/-- The relative Fox derivative of a free generator is the corresponding coordinate vector. -/
@[simp]
theorem relativeFreeGroupFoxDerivative_of (x : X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (FreeGroup.of x) =
      Pi.single x (1 : GroupRing H) := by
  simp only [relativeFreeGroupFoxDerivative, relativeFreeGroupFoxLift,
    FreeGroup.lift_apply_of, toAdd_ofAdd]

/-- Relative Fox product rule. -/
theorem relativeFreeGroupFoxDerivative_mul (w₁ w₂ : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (w₁ * w₂) =
      relativeFreeGroupFoxDerivative (H := H) X ψ w₁ +
        (MonoidAlgebra.of ℤ H (ψ w₁) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ w₂ := by
  simp only [relativeFreeGroupFoxDerivative, map_mul, SemidirectProduct.mul_left,
    toAdd_mul, crossedSemidirectMulAction_toAdd, scalarCrossedAction_apply,
    relativeFreeGroupFoxLift_right, groupRingScalar_apply, MonoidHom.id_apply]

/-- The relative free-group Fox derivative is a differential map for \(\psi\). -/
def relativeFreeGroupFoxHom :
    DifferentialHom ψ (RelativeFreeFoxCoordinates (H := H) X) where
  toFun := relativeFreeGroupFoxDerivative (H := H) X ψ
  map_mul' := by
    intro w₁ w₂
    simpa only [scalarCrossedAction_apply, groupRingScalar_apply] using
      relativeFreeGroupFoxDerivative_mul (H := H) X ψ w₁ w₂

/-- The bundled relative Fox crossed homomorphism evaluates to the relative Fox
derivative. -/
@[simp]
theorem relativeFreeGroupFoxHom_apply (w : FreeGroup X) :
    relativeFreeGroupFoxHom (H := H) X ψ w =
      relativeFreeGroupFoxDerivative (H := H) X ψ w :=
  rfl

/-- The relative Fox derivative satisfies the inverse rule. -/
theorem relativeFreeGroupFoxDerivative_inv (w : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ w⁻¹ =
      -((MonoidAlgebra.of ℤ H (ψ w⁻¹) : GroupRing H) •
        relativeFreeGroupFoxDerivative (H := H) X ψ w) := by
  simpa only [groupRingScalar_apply, relativeFreeGroupFoxHom_apply] using
    ScalarCrossedHom.map_inv (relativeFreeGroupFoxHom (H := H) X ψ) w

/--
Uniqueness of the relative free-group Fox derivative among differential maps with standard
coordinate values on free generators.
-/
theorem relativeFreeGroupFoxHom_unique
    (delta : DifferentialHom ψ (RelativeFreeFoxCoordinates (H := H) X))
    (hbasis :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : GroupRing H)) :
    delta = relativeFreeGroupFoxHom (H := H) X ψ := by
  have hdelta_free :=
    freeCrossedHomWithCoeff_unique
      (A := RelativeFreeFoxCoordinates (H := H) X) (groupRingScalar ψ)
      (fun x : X => Pi.single x (1 : GroupRing H)) delta hbasis
  have hrelative_free :=
    freeCrossedHomWithCoeff_unique
      (A := RelativeFreeFoxCoordinates (H := H) X) (groupRingScalar ψ)
      (fun x : X => Pi.single x (1 : GroupRing H))
      (relativeFreeGroupFoxHom (H := H) X ψ)
      (relativeFreeGroupFoxDerivative_of (H := H) X ψ)
  exact hdelta_free.trans hrelative_free.symm

/-- Relative Fox derivative of a positive power. -/
theorem relativeFreeGroupFoxDerivative_pow (w : FreeGroup X) (n : ℕ) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (w ^ n) =
      (Finset.range n).sum (fun k =>
        (MonoidAlgebra.of ℤ H (ψ (w ^ k)) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ w) := by
  simpa only [relativeFreeGroupFoxHom_apply, groupRingScalar_apply, map_pow] using
    ScalarCrossedHom.map_pow (relativeFreeGroupFoxHom (H := H) X ψ) w n

/-- Relative Fox derivative of a conjugate. -/
theorem relativeFreeGroupFoxDerivative_conj (g h : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ (g * h * g⁻¹) =
      relativeFreeGroupFoxDerivative (H := H) X ψ g +
        (MonoidAlgebra.of ℤ H (ψ g) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ h -
        (MonoidAlgebra.of ℤ H (ψ (g * h * g⁻¹)) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ g := by
  simpa only [relativeFreeGroupFoxHom_apply, groupRingScalar_apply] using
    ScalarCrossedHom.map_conj
      (coeff := groupRingScalar ψ) (relativeFreeGroupFoxHom (H := H) X ψ) g h

/-- Relative Fox derivative of a commutator. -/
theorem relativeFreeGroupFoxDerivative_commutator (g h : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) X ψ ⁅g, h⁆ =
      relativeFreeGroupFoxDerivative (H := H) X ψ g +
        (MonoidAlgebra.of ℤ H (ψ g) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ h -
        (MonoidAlgebra.of ℤ H (ψ (g * h * g⁻¹)) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ g -
        (MonoidAlgebra.of ℤ H (ψ ⁅g, h⁆) : GroupRing H) •
          relativeFreeGroupFoxDerivative (H := H) X ψ h := by
  simpa only [relativeFreeGroupFoxHom_apply, groupRingScalar_apply] using
    ScalarCrossedHom.map_commutator (relativeFreeGroupFoxHom (H := H) X ψ) g h

end FoxCalculus

end

end FoxDifferential
