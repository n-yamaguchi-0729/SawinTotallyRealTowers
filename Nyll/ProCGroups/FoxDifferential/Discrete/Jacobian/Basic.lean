/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.Absolute

/-!
# Fox differential: discrete — jacobian — basic

The principal declarations in this module are:

- `freeGroupHomFoxJacobian`
  The relative Fox Jacobian of \(\varphi : \mathrm{FreeGroup}(X) \to \mathrm{FreeGroup}(Y)\), with
  coefficients pushed forward by \(\psi : \mathrm{FreeGroup}(Y) \to H\). The row indexed by \(x :
  X\) is the relative Fox derivative of the substituted generator \(\varphi(x)\) with respect to the
  \(Y\)-generators.
- `freeGroupHomFoxJacobianMatrix`
  The relative Fox Jacobian, packaged as a matrix.
- `freeGroupHomFoxJacobianMatrix_apply`
  Evaluating the bundled relative Fox Jacobian matrix at `(x, y)` returns the corresponding relative
  Fox derivative.
- `freeGroupHomFoxJacobian_eq_freeCrossedDifferentialWithCoeffJacobian`
  The usual relative Fox Jacobian is the coefficient-generic free crossed-differential Jacobian
  specialized to the group-ring coefficient homomorphism.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators

universe u v w z t

variable {H : Type w} [Group H]
variable {X : Type u} {Y : Type v}

/--
The relative Fox Jacobian of \(\varphi : \mathrm{FreeGroup}(X) \to \mathrm{FreeGroup}(Y)\), with
coefficients pushed forward by \(\psi : \mathrm{FreeGroup}(Y) \to H\). The row indexed by \(x :
X\) is the relative Fox derivative of the substituted generator \(\varphi(x)\) with respect to
the \(Y\)-generators.
-/
def freeGroupHomFoxJacobian
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    X → Y → GroupRing H :=
  fun x =>
    relativeFreeGroupFoxDerivative (H := H) Y ψ (φ (FreeGroup.of x))

/-- The relative Fox Jacobian, packaged as a matrix. -/
def freeGroupHomFoxJacobianMatrix
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    Matrix X Y (GroupRing H) :=
  freeGroupHomFoxJacobian (H := H) ψ φ

/--
Evaluating the bundled relative Fox Jacobian matrix at `(x, y)` returns the corresponding relative
Fox derivative.
-/
@[simp]
theorem freeGroupHomFoxJacobianMatrix_apply
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (x : X) (y : Y) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ φ x y =
    freeGroupHomFoxJacobian (H := H) ψ φ x y :=
  rfl

/--
The usual relative Fox Jacobian is the coefficient-generic free crossed-differential Jacobian
specialized to the group-ring coefficient homomorphism.
-/
theorem freeGroupHomFoxJacobian_eq_freeCrossedDifferentialWithCoeffJacobian
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobian (H := H) ψ φ =
      freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (groupRingScalar ψ) φ := by
  funext x y
  simp only [freeGroupHomFoxJacobian, freeCrossedDifferentialWithCoeffJacobian,
  freeCrossedDifferentialWithCoeffCoordinates_eq_relativeFreeGroupFoxDerivative]

/--
Matrix form of the comparison between the usual relative Fox Jacobian and the
coefficient-generic free crossed-differential Jacobian.
-/
theorem freeGroupHomFoxJacobianMatrix_eq_freeCrossedDifferentialWithCoeffJacobianMatrix
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ φ =
      freeCrossedDifferentialWithCoeffJacobianMatrix
        (X := X) (Y := Y) (groupRingScalar ψ) φ := by
  apply Matrix.ext
  intro x y
  simp only [freeGroupHomFoxJacobianMatrix_apply,
  freeGroupHomFoxJacobian_eq_freeCrossedDifferentialWithCoeffJacobian,
  freeCrossedDifferentialWithCoeffJacobianMatrix_apply]

/-- The absolute Fox Jacobian of a homomorphism between free groups. -/
def freeGroupHomFoxJacobianAbsolute
    [DecidableEq Y]
    (φ : FreeGroup X →* FreeGroup Y) :
    X → Y → GroupRing (FreeGroup Y) :=
  freeGroupHomFoxJacobian (H := FreeGroup Y) (MonoidHom.id (FreeGroup Y)) φ

/-- The absolute Fox Jacobian, packaged as a matrix. -/
def freeGroupHomFoxJacobianAbsoluteMatrix
    [DecidableEq Y]
    (φ : FreeGroup X →* FreeGroup Y) :
    Matrix X Y (GroupRing (FreeGroup Y)) :=
  freeGroupHomFoxJacobianAbsolute φ

/--
Evaluating the bundled absolute Fox Jacobian matrix at `(x, y)` returns the corresponding absolute
Fox derivative.
-/
@[simp]
theorem freeGroupHomFoxJacobianAbsoluteMatrix_apply
    [DecidableEq Y]
    (φ : FreeGroup X →* FreeGroup Y) (x : X) (y : Y) :
    freeGroupHomFoxJacobianAbsoluteMatrix φ x y =
      freeGroupHomFoxJacobianAbsolute φ x y :=
  rfl

/-- The absolute Fox Jacobian of the identity homomorphism is the coordinate identity family. -/
@[simp]
theorem freeGroupHomFoxJacobianAbsolute_id
    [DecidableEq X] :
    freeGroupHomFoxJacobianAbsolute (MonoidHom.id (FreeGroup X)) =
      fun x : X => Pi.single x (1 : GroupRing (FreeGroup X)) := by
  funext x y
  simp only [freeGroupHomFoxJacobianAbsolute, freeGroupHomFoxJacobian, MonoidHom.id_apply,
  relativeFreeGroupFoxDerivative_of]

/-- The absolute Fox Jacobian matrix of the identity homomorphism is the identity matrix. -/
@[simp]
theorem freeGroupHomFoxJacobianAbsoluteMatrix_id
    [DecidableEq X] :
    freeGroupHomFoxJacobianAbsoluteMatrix (MonoidHom.id (FreeGroup X)) =
      (1 : Matrix X X (GroupRing (FreeGroup X))) := by
  apply Matrix.ext
  intro x y
  change freeGroupHomFoxJacobianAbsolute (MonoidHom.id (FreeGroup X)) x y =
    (1 : Matrix X X (GroupRing (FreeGroup X))) x y
  rw [show
      freeGroupHomFoxJacobianAbsolute (MonoidHom.id (FreeGroup X)) x y =
        (Pi.single x (1 : GroupRing (FreeGroup X)) : X → GroupRing (FreeGroup X)) y from
      congrFun (congrFun freeGroupHomFoxJacobianAbsolute_id x) y]
  by_cases hxy : x = y
  · subst y
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [ne_eq, hxy, not_false_eq_true, Pi.single_eq_of_ne', Matrix.one_apply_ne]

variable {K : Type t} [Group K]

/--
Postcomposing the coefficient homomorphism maps each relative Fox Jacobian entry through the induced
group-ring map.
-/
theorem freeGroupHomFoxJacobian_mapDomain_apply
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (η : H →* K)
    (φ : FreeGroup X →* FreeGroup Y) (x : X) (y : Y) :
    freeGroupHomFoxJacobian (H := K) (η.comp ψ) φ x y =
      groupRingMap η (freeGroupHomFoxJacobian (H := H) ψ φ x y) := by
  simp only [freeGroupHomFoxJacobian, relativeFreeGroupFoxDerivative_mapDomain_apply]

/-- Fox Jacobians are natural under coefficient push-forward, matrix form. -/
theorem freeGroupHomFoxJacobianMatrix_mapDomain
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (η : H →* K)
    (φ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobianMatrix (H := K) (η.comp ψ) φ =
      (freeGroupHomFoxJacobianMatrix (H := H) ψ φ).map (groupRingMap η) := by
  apply Matrix.ext
  intro x y
  change
    freeGroupHomFoxJacobian (H := K) (η.comp ψ) φ x y =
      groupRingMap η (freeGroupHomFoxJacobian (H := H) ψ φ x y)
  exact freeGroupHomFoxJacobian_mapDomain_apply ψ η φ x y

/--
A relative Fox Jacobian entry is the image of the corresponding absolute entry under the coefficient
group-ring map.
-/
theorem freeGroupHomFoxJacobian_eq_map_absolute_apply
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y)
    (x : X) (y : Y) :
    freeGroupHomFoxJacobian (H := H) ψ φ x y =
      groupRingMap ψ (freeGroupHomFoxJacobianAbsolute φ x y) := by
  simpa [freeGroupHomFoxJacobianAbsolute] using
    freeGroupHomFoxJacobian_mapDomain_apply
      (H := FreeGroup Y) (K := H)
      (MonoidHom.id (FreeGroup Y)) ψ φ x y

/-- Matrix form of the absolute-to-relative comparison for Fox Jacobians. -/
theorem freeGroupHomFoxJacobianMatrix_eq_map_absolute
    [DecidableEq Y]
    (ψ : FreeGroup Y →* H) (φ : FreeGroup X →* FreeGroup Y) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ φ =
      (freeGroupHomFoxJacobianAbsoluteMatrix φ).map (groupRingMap ψ) := by
  apply Matrix.ext
  intro x y
  change
    freeGroupHomFoxJacobian (H := H) ψ φ x y =
      groupRingMap ψ (freeGroupHomFoxJacobianAbsolute φ x y)
  exact freeGroupHomFoxJacobian_eq_map_absolute_apply ψ φ x y


end FoxCalculus

end

end FoxDifferential
