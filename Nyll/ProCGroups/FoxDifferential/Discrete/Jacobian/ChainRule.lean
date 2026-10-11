/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.Jacobian.Basic

/-!
# Fox differential: discrete — jacobian — chain rule

The principal declarations in this module are:

- `relativeFreeGroupFoxHom_comp`
  The composed derivative \(w \mapsto D(\varphi(w))\) is a crossed differential.
- `relativeFreeGroupFoxDerivative_comp_apply`
  The relative Fox derivative of a composite free-group homomorphism satisfies the coordinatewise
  chain-rule sum.
- `relativeFreeGroupFoxDerivative_comp`
  Fox chain rule for homomorphisms between free groups in vector form.
- `freeGroupHomFoxJacobian_id`
  The relative Fox Jacobian of the identity homomorphism is the coordinate identity family.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators

universe u v w z t

variable {H : Type w} [Group H]
variable {X : Type u} {Y : Type v}

/-- The composed derivative \(w \mapsto D(\varphi(w))\) is a crossed differential. -/
def relativeFreeGroupFoxHom_comp
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    DifferentialHom (ψ.comp φ) (Y → GroupRing H) where
  toFun w := relativeFreeGroupFoxHom (H := H) Y ψ (φ w)
  map_mul' := by
    intro u v
    funext y
    simp only [scalarCrossedAction_apply, map_mul, ScalarCrossedHom.map_mul,
      MonoidAlgebra.of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      groupRingScalar, MonoidHom.coe_comp, Function.comp_apply]
    rfl

/--
The relative Fox derivative of a composite free-group homomorphism satisfies the coordinatewise
chain-rule sum.
-/
theorem relativeFreeGroupFoxDerivative_comp_apply
    [DecidableEq X] [Fintype X] [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) (y : Y) :
    relativeFreeGroupFoxDerivative (H := H) Y ψ (φ w) y =
      ∑ x : X,
        relativeFreeGroupFoxDerivative (H := H) X (ψ.comp φ) w x *
          freeGroupHomFoxJacobian (H := H) ψ φ x y := by
  have h :=
    crossedHom_comp_relativeFreeGroupFoxDerivative
      (H := H) (A := Y → GroupRing H) (X := X) (Y := Y)
      ψ φ (relativeFreeGroupFoxHom (H := H) Y ψ) w
  have hy := congrFun h y
  simpa [freeGroupHomFoxJacobian, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hy

/-- Fox chain rule for homomorphisms between free groups in vector form. -/
theorem relativeFreeGroupFoxDerivative_comp
    [DecidableEq X] [Fintype X] [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    relativeFreeGroupFoxDerivative (H := H) Y ψ (φ w) =
      fun y : Y =>
        ∑ x : X,
          relativeFreeGroupFoxDerivative (H := H) X (ψ.comp φ) w x *
            freeGroupHomFoxJacobian (H := H) ψ φ x y := by
  funext y
  exact relativeFreeGroupFoxDerivative_comp_apply (H := H) ψ φ w y

/-- The relative Fox Jacobian of the identity homomorphism is the coordinate identity family. -/
@[simp]
theorem freeGroupHomFoxJacobian_id
    [DecidableEq X]
    (ψ : FreeGroup X →* H) :
    freeGroupHomFoxJacobian (H := H) ψ (MonoidHom.id (FreeGroup X)) =
      fun x : X => Pi.single x (1 : GroupRing H) := by
  funext x y
  simp only [freeGroupHomFoxJacobian, MonoidHom.id_apply, relativeFreeGroupFoxDerivative_of]

variable {Z : Type z}

/--
An entry of the relative Fox Jacobian of a composite is the group-ring-weighted sum of the
corresponding Jacobian entries.
-/
theorem freeGroupHomFoxJacobian_comp_apply
    [DecidableEq Y] [Fintype Y] [DecidableEq Z]
    (ψ : FreeGroup Z →* H)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y)
    (x : X) (z : Z) :
    freeGroupHomFoxJacobian (H := H) ψ (φ.comp χ) x z =
      ∑ y : Y,
        freeGroupHomFoxJacobian (H := H) (ψ.comp φ) χ x y *
          freeGroupHomFoxJacobian (H := H) ψ φ y z := by
  simpa [freeGroupHomFoxJacobian] using
    relativeFreeGroupFoxDerivative_comp_apply (H := H) ψ φ (χ (FreeGroup.of x)) z

/--
The Fox Jacobian chain rule for homomorphisms between free groups is expressed in matrix form.
-/
theorem freeGroupHomFoxJacobian_comp
    [DecidableEq Y] [Fintype Y] [DecidableEq Z]
    (ψ : FreeGroup Z →* H)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobian (H := H) ψ (φ.comp χ) =
      fun x z =>
        ∑ y : Y,
          freeGroupHomFoxJacobian (H := H) (ψ.comp φ) χ x y *
            freeGroupHomFoxJacobian (H := H) ψ φ y z := by
  funext x z
  exact freeGroupHomFoxJacobian_comp_apply (H := H) ψ φ χ x z

/-- The relative Fox Jacobian matrix of the identity homomorphism is the identity matrix. -/
@[simp]
theorem freeGroupHomFoxJacobianMatrix_id
    [DecidableEq X]
    (ψ : FreeGroup X →* H) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ (MonoidHom.id (FreeGroup X)) =
      (1 : Matrix X X (GroupRing H)) := by
  apply Matrix.ext
  intro x y
  change freeGroupHomFoxJacobian (H := H) ψ (MonoidHom.id (FreeGroup X)) x y =
    (1 : Matrix X X (GroupRing H)) x y
  rw [show
      freeGroupHomFoxJacobian (H := H) ψ (MonoidHom.id (FreeGroup X)) x y =
        (Pi.single x (1 : GroupRing H) : X → GroupRing H) y from
      congrFun (congrFun (freeGroupHomFoxJacobian_id (H := H) ψ) x) y]
  by_cases hxy : x = y
  · subst y
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [ne_eq, hxy, not_false_eq_true, Pi.single_eq_of_ne', Matrix.one_apply_ne]

/-- Fox Jacobian chain rule, packaged as matrix multiplication. -/
theorem freeGroupHomFoxJacobianMatrix_comp
    [DecidableEq Y] [Fintype Y] [DecidableEq Z]
    (ψ : FreeGroup Z →* H)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ (φ.comp χ) =
      freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp φ) χ *
        freeGroupHomFoxJacobianMatrix (H := H) ψ φ := by
  apply Matrix.ext
  intro x z
  change
    freeGroupHomFoxJacobian (H := H) ψ (φ.comp χ) x z =
      ∑ y : Y,
        freeGroupHomFoxJacobian (H := H) (ψ.comp φ) χ x y *
          freeGroupHomFoxJacobian (H := H) ψ φ y z
  exact freeGroupHomFoxJacobian_comp_apply
    (H := H) (X := X) (Y := Y) (Z := Z) ψ φ χ x z

/--
An entry of the absolute Fox Jacobian of a composite is the group-ring-weighted chain-rule sum.
-/
theorem freeGroupHomFoxJacobianAbsolute_comp_apply
    [DecidableEq Y] [Fintype Y] [DecidableEq Z]
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y)
    (x : X) (z : Z) :
    freeGroupHomFoxJacobianAbsolute (φ.comp χ) x z =
      ∑ y : Y,
        groupRingMap φ (freeGroupHomFoxJacobianAbsolute χ x y) *
          freeGroupHomFoxJacobianAbsolute φ y z := by
  calc
    freeGroupHomFoxJacobianAbsolute (φ.comp χ) x z =
        ∑ y : Y,
          freeGroupHomFoxJacobian (H := FreeGroup Z) φ χ x y *
            freeGroupHomFoxJacobianAbsolute φ y z := by
      simpa [freeGroupHomFoxJacobianAbsolute] using
        freeGroupHomFoxJacobian_comp_apply
          (H := FreeGroup Z)
          (X := X) (Y := Y) (Z := Z)
          (MonoidHom.id (FreeGroup Z)) φ χ x z
    _ =
        ∑ y : Y,
          groupRingMap φ (freeGroupHomFoxJacobianAbsolute χ x y) *
            freeGroupHomFoxJacobianAbsolute φ y z := by
      apply Finset.sum_congr rfl
      intro y _
      rw [freeGroupHomFoxJacobian_eq_map_absolute_apply (H := FreeGroup Z) φ χ x y]

/-- The absolute Fox Jacobian chain rule is expressed in matrix form. -/
theorem freeGroupHomFoxJacobianAbsoluteMatrix_comp
    [DecidableEq Y] [Fintype Y] [DecidableEq Z]
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobianAbsoluteMatrix (φ.comp χ) =
      (freeGroupHomFoxJacobianAbsoluteMatrix χ).map (groupRingMap φ) *
        freeGroupHomFoxJacobianAbsoluteMatrix φ := by
  apply Matrix.ext
  intro x z
  change
    freeGroupHomFoxJacobianAbsolute (φ.comp χ) x z =
      ∑ y : Y,
        groupRingMap φ (freeGroupHomFoxJacobianAbsolute χ x y) *
          freeGroupHomFoxJacobianAbsolute φ y z
  exact freeGroupHomFoxJacobianAbsolute_comp_apply
    (X := X) (Y := Y) (Z := Z) φ χ x z


end FoxCalculus

end

end FoxDifferential
