/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.Jacobian.ChainRule

/-!
# Fox differential: discrete — jacobian — automorphism

The principal declarations in this module are:

- `freeGroupAutomorphismFoxJacobianMatrixInverse`
  The named inverse matrix for the Fox Jacobian of a free-group automorphism. For \(J_{\psi}(e)\),
  the inverse is the Jacobian of the inverse automorphism \(e^{-1}\), with coefficients pushed
  forward by the composite of \(\psi\) and the monoid homomorphism underlying \(e\).
- `freeGroupAutomorphismFoxJacobian_left_inverse_apply`
  The Fox Jacobian of a free-group automorphism, multiplied on the left by the Jacobian of its
  inverse, has Kronecker-delta entries.
- `freeGroupAutomorphismFoxJacobian_right_inverse_apply`
  The Fox Jacobian of a free-group automorphism, multiplied on the right by the Jacobian of its
  inverse, has Kronecker-delta entries.
- `freeGroupAutomorphismFoxJacobianMatrix_left_inverse`
  The Jacobian matrix of a free-group automorphism has the expected left inverse.
-/

namespace FoxDifferential

noncomputable section

namespace FoxCalculus

open scoped BigOperators

universe u v w z t

variable {H : Type w} [Group H]
variable {X : Type u} {Y : Type v}
/--
The Fox Jacobian of a free-group automorphism, multiplied on the left by the Jacobian of its
inverse, has Kronecker-delta entries.
-/
theorem freeGroupAutomorphismFoxJacobian_left_inverse_apply
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X)
    (x z : X) :
    (∑ y : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.toMonoidHom)
          e.symm.toMonoidHom x y *
          freeGroupHomFoxJacobian (H := H) ψ e.toMonoidHom y z) =
      (Pi.single x (1 : GroupRing H) : X → GroupRing H) z := by
  have h :=
    freeGroupHomFoxJacobian_comp_apply (H := H)
      (X := X) (Y := X) (Z := X) ψ e.toMonoidHom e.symm.toMonoidHom x z
  have hid :
      e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (FreeGroup X) := by
    ext w
    simp only [MulEquiv.toMonoidHom_eq_coe, MulEquiv.toMonoidHom_comp_toMonoidHom_symm,
        MonoidHom.id_apply]
  rw [hid, freeGroupHomFoxJacobian_id] at h
  simpa using h.symm

/--
The Fox Jacobian of a free-group automorphism, multiplied on the right by the Jacobian of its
inverse, has Kronecker-delta entries.
-/
theorem freeGroupAutomorphismFoxJacobian_right_inverse_apply
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X)
    (x z : X) :
    (∑ y : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.symm.toMonoidHom)
          e.toMonoidHom x y *
          freeGroupHomFoxJacobian (H := H) ψ e.symm.toMonoidHom y z) =
      (Pi.single x (1 : GroupRing H) : X → GroupRing H) z := by
  have h :=
    freeGroupHomFoxJacobian_comp_apply (H := H)
      (X := X) (Y := X) (Z := X) ψ e.symm.toMonoidHom e.toMonoidHom x z
  have hid :
      e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id (FreeGroup X) := by
    ext w
    simp only [MulEquiv.toMonoidHom_eq_coe, MulEquiv.toMonoidHom_symm_comp_toMonoidHom,
        MonoidHom.id_apply]
  rw [hid, freeGroupHomFoxJacobian_id] at h
  simpa using h.symm

/-- The Jacobian matrix of a free-group automorphism has the expected left inverse. -/
theorem freeGroupAutomorphismFoxJacobianMatrix_left_inverse
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp e.toMonoidHom)
        e.symm.toMonoidHom *
      freeGroupHomFoxJacobianMatrix (H := H) ψ e.toMonoidHom =
      (1 : Matrix X X (GroupRing H)) := by
  apply Matrix.ext
  intro x z
  change
    (∑ j : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.toMonoidHom)
          e.symm.toMonoidHom x j *
          freeGroupHomFoxJacobian (H := H) ψ e.toMonoidHom j z) =
      (1 : Matrix X X (GroupRing H)) x z
  rw [show
      (∑ j : X,
          freeGroupHomFoxJacobian (H := H) (ψ.comp e.toMonoidHom)
            e.symm.toMonoidHom x j *
            freeGroupHomFoxJacobian (H := H) ψ e.toMonoidHom j z) =
        (Pi.single x (1 : GroupRing H) : X → GroupRing H) z from
      freeGroupAutomorphismFoxJacobian_left_inverse_apply (H := H) ψ e x z]
  by_cases hxz : x = z
  · subst z
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [ne_eq, hxz, not_false_eq_true, Pi.single_eq_of_ne', Matrix.one_apply_ne]

/-- The Jacobian matrix of a free-group automorphism has the expected right inverse. -/
theorem freeGroupAutomorphismFoxJacobianMatrix_right_inverse
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp e.symm.toMonoidHom)
        e.toMonoidHom *
      freeGroupHomFoxJacobianMatrix (H := H) ψ e.symm.toMonoidHom =
      (1 : Matrix X X (GroupRing H)) := by
  apply Matrix.ext
  intro x z
  change
    (∑ j : X,
        freeGroupHomFoxJacobian (H := H) (ψ.comp e.symm.toMonoidHom)
          e.toMonoidHom x j *
          freeGroupHomFoxJacobian (H := H) ψ e.symm.toMonoidHom j z) =
      (1 : Matrix X X (GroupRing H)) x z
  rw [show
      (∑ j : X,
          freeGroupHomFoxJacobian (H := H) (ψ.comp e.symm.toMonoidHom)
            e.toMonoidHom x j *
            freeGroupHomFoxJacobian (H := H) ψ e.symm.toMonoidHom j z) =
        (Pi.single x (1 : GroupRing H) : X → GroupRing H) z from
      freeGroupAutomorphismFoxJacobian_right_inverse_apply (H := H) ψ e x z]
  by_cases hxz : x = z
  · subst z
    simp only [Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [ne_eq, hxz, not_false_eq_true, Pi.single_eq_of_ne', Matrix.one_apply_ne]

/--
The named inverse matrix for the Fox Jacobian of a free-group automorphism. For \(J_{\psi}(e)\),
the inverse is the Jacobian of the inverse automorphism \(e^{-1}\), with coefficients pushed
forward by the composite of \(\psi\) and the monoid homomorphism underlying \(e\).
-/
def freeGroupAutomorphismFoxJacobianMatrixInverse
    [DecidableEq X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    Matrix X X (GroupRing H) :=
  freeGroupHomFoxJacobianMatrix (H := H) (ψ.comp e.toMonoidHom) e.symm.toMonoidHom

/-- The named inverse matrix is a left inverse for the Fox Jacobian of a free-group automorphism. -/
theorem freeGroupAutomorphismFoxJacobianMatrixInverse_mul
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupAutomorphismFoxJacobianMatrixInverse (H := H) ψ e *
        freeGroupHomFoxJacobianMatrix (H := H) ψ e.toMonoidHom =
      (1 : Matrix X X (GroupRing H)) := by
  simpa [freeGroupAutomorphismFoxJacobianMatrixInverse] using
    freeGroupAutomorphismFoxJacobianMatrix_left_inverse (H := H) ψ e

/--
The named inverse matrix is a right inverse for the Fox Jacobian of a free-group automorphism.
-/
theorem freeGroupAutomorphismFoxJacobianMatrix_mul_inverse
    [DecidableEq X] [Fintype X]
    (ψ : FreeGroup X →* H) (e : FreeGroup X ≃* FreeGroup X) :
    freeGroupHomFoxJacobianMatrix (H := H) ψ e.toMonoidHom *
        freeGroupAutomorphismFoxJacobianMatrixInverse (H := H) ψ e =
      (1 : Matrix X X (GroupRing H)) := by
  have h :=
    freeGroupAutomorphismFoxJacobianMatrix_right_inverse (H := H)
      (ψ.comp e.toMonoidHom) e
  have hcomp :
      (ψ.comp e.toMonoidHom).comp e.symm.toMonoidHom = ψ := by
    ext w
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
        Function.comp_apply,
  MulEquiv.apply_symm_apply]
  rw [hcomp] at h
  simpa [freeGroupAutomorphismFoxJacobianMatrixInverse] using h


end FoxCalculus

end

end FoxDifferential
