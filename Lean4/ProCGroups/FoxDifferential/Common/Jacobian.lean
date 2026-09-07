import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false

/-!
# Fox differential: common — jacobian

The principal declarations in this module are:

- `foxJacobianMatrix`
  A Fox-Jacobian family packaged as a finite matrix.
- `foxJacobianId`
  The identity Fox-Jacobian family with Kronecker-delta entries.
- `foxJacobianMatrix_apply`
  The packaged Fox-Jacobian matrix entry is the corresponding Jacobian family entry.
- `foxJacobianId_apply`
  The identity Fox-Jacobian evaluates to the Kronecker-delta coefficient at the chosen pair of
  indices.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v w z

section JacobianLinearMap

variable {R : Type u} [Ring R]
variable {X : Type v}
variable {Y : Type w}

/-- A Fox-Jacobian family packaged as a finite matrix. -/
def foxJacobianMatrix (jac : X → Y → R) : Matrix X Y R :=
  jac

omit [Ring R] in
/-- The packaged Fox-Jacobian matrix entry is the corresponding Jacobian family entry. -/
@[simp]
theorem foxJacobianMatrix_apply (jac : X → Y → R) (x : X) (y : Y) :
    foxJacobianMatrix jac x y = jac x y :=
  rfl

section Identity

variable [DecidableEq X]

/-- The identity Fox-Jacobian family with Kronecker-delta entries. -/
def foxJacobianId : X → X → R := fun x => Pi.single x (1 : R)

/--
The identity Fox-Jacobian evaluates to the Kronecker-delta coefficient at the chosen pair of
indices.
-/
@[simp]
theorem foxJacobianId_apply (x y : X) :
    foxJacobianId (R := R) (X := X) x y = (Pi.single x (1 : R) : X → R) y :=
  rfl

/-- The identity Fox-Jacobian family is the identity matrix. -/
@[simp]
theorem foxJacobianMatrix_id :
    foxJacobianMatrix (R := R) (X := X) (Y := X) (foxJacobianId (R := R) (X := X)) =
      (1 : Matrix X X R) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [foxJacobianMatrix, foxJacobianId, Pi.single_eq_same, Matrix.one_apply_eq]
  · simp only [foxJacobianMatrix, foxJacobianId, ne_eq, hxy, not_false_eq_true, Pi.single_eq_of_ne',
  Matrix.one_apply_ne]

end Identity

/--
A Fox-Jacobian family determines the corresponding finite linear map between free coefficient
modules.
-/
def foxJacobianLinearMap [Fintype X] (jac : X → Y → R) :
    (X → R) →ₗ[R] (Y → R) where
  toFun v := fun y => ∑ x : X, v x * jac x y
  map_add' v w := by
    funext y
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a v := by
    funext y
    simp only [Pi.smul_apply]
    change (∑ x : X, (a * v x) * jac x y) = a * ∑ x : X, v x * jac x y
    simp only [mul_assoc, Finset.mul_sum]

/--
The linear map associated with a Fox-Jacobian family is evaluated by the finite matrix
coefficient formula.
-/
@[simp]
theorem foxJacobianLinearMap_apply
    [Fintype X]
    (jac : X → Y → R) (v : X → R) (y : Y) :
    foxJacobianLinearMap jac v y = ∑ x : X, v x * jac x y :=
  rfl

/-- The Fox-Jacobian linear map is row-vector multiplication by the corresponding matrix. -/
theorem foxJacobianLinearMap_eq_vecMul
    [Fintype X]
    (jac : X → Y → R) (v : X → R) :
    foxJacobianLinearMap jac v = Matrix.vecMul v (foxJacobianMatrix jac) := by
  funext y
  simp only [foxJacobianLinearMap_apply, Matrix.vecMul, dotProduct, foxJacobianMatrix]

/--
The identity Fox-Jacobian induces the identity linear map on the finite free coefficient module.
-/
@[simp]
theorem foxJacobianLinearMap_id [Fintype X] [DecidableEq X] :
    foxJacobianLinearMap (R := R) (X := X) (Y := X) (foxJacobianId (R := R) (X := X)) =
      (LinearMap.id : (X → R) →ₗ[R] (X → R)) := by
  apply LinearMap.ext
  intro v
  funext y
  change (∑ x : X, v x * (Pi.single x (1 : R) : X → R) y) = v y
  rw [Finset.sum_eq_single y]
  · simp only [Pi.single_eq_same, mul_one]
  · intro x _ hxy
    rw [Pi.single_eq_of_ne (Ne.symm hxy)]
    simp only [mul_zero]
  · intro hy
    simp only [Finset.mem_univ, not_true_eq_false] at hy

variable {Z : Type z}

/--
Composition of finite Fox-Jacobian linear maps is given by multiplication of the corresponding
Jacobian matrices.
-/
theorem foxJacobianLinearMap_comp
    [Fintype X] [Fintype Y]
    (jacXY : X → Y → R) (jacYZ : Y → Z → R) :
    (foxJacobianLinearMap jacYZ).comp (foxJacobianLinearMap jacXY) =
      foxJacobianLinearMap (fun x z => ∑ y : Y, jacXY x y * jacYZ y z) := by
  ext v z
  change
    (∑ y : Y, (∑ x : X, v x * jacXY x y) * jacYZ y z) =
      ∑ x : X, v x * ∑ y : Y, jacXY x y * jacYZ y z
  calc
    (∑ y : Y, (∑ x : X, v x * jacXY x y) * jacYZ y z) =
        ∑ y : Y, ∑ x : X, (v x * jacXY x y) * jacYZ y z := by
          simp only [Finset.sum_mul]
    _ = ∑ x : X, ∑ y : Y, (v x * jacXY x y) * jacYZ y z := by
          rw [Finset.sum_comm]
    _ = ∑ x : X, v x * ∑ y : Y, jacXY x y * jacYZ y z := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [mul_assoc]

/-- Composition of Fox-Jacobian matrices is finite matrix multiplication. -/
theorem foxJacobianMatrix_comp
    [Fintype Y]
    (jacXY : X → Y → R) (jacYZ : Y → Z → R) :
    foxJacobianMatrix (R := R) (X := X) (Y := Z)
        (fun x z => ∑ y : Y, jacXY x y * jacYZ y z) =
      foxJacobianMatrix (R := R) (X := X) (Y := Y) jacXY *
        foxJacobianMatrix (R := R) (X := Y) (Y := Z) jacYZ := by
  apply Matrix.ext
  intro x z
  exact
    (Matrix.mul_apply
      (M := foxJacobianMatrix (R := R) (X := X) (Y := Y) jacXY)
      (N := foxJacobianMatrix (R := R) (X := Y) (Y := Z) jacYZ)).symm

/--
A Fox-Jacobian linear map sends a standard source coordinate to the corresponding Jacobian row.
-/
@[simp]
theorem foxJacobianLinearMap_single [Fintype X] [DecidableEq X] (jac : X → Y → R) (x : X) :
    foxJacobianLinearMap jac (Pi.single x (1 : R)) = jac x := by
  funext y
  change (∑ z : X, ((Pi.single x (1 : R) : X → R) z) * jac z y) = jac x y
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_mul]
  · intro z _ hz
    simp only [Pi.single_eq_of_ne hz, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_mul, IsEmpty.forall_iff]

variable {M : Type*} [AddCommMonoid M] [Module R M]

/--
Linear maps out of finite coordinate vectors are determined by their values on the standard
coordinate vectors.
-/
theorem linearMap_ext_pi_single
    [Finite X] [DecidableEq X]
    {L₁ L₂ : (X → R) →ₗ[R] M}
    (h : ∀ x : X, L₁ (Pi.single x (1 : R)) = L₂ (Pi.single x (1 : R))) :
    L₁ = L₂ := by
  classical
  let : Fintype X := Fintype.ofFinite X
  apply LinearMap.ext
  intro v
  have hv : v = ∑ x : X, v x • (Pi.single x (1 : R) : X → R) := by
    funext y
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single y]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro x _ hxy
      change v x * ((Pi.single x (1 : R) : X → R) y) = 0
      rw [Pi.single_eq_of_ne (Ne.symm hxy)]
      simp only [mul_zero]
    · intro hy
      simp only [Finset.mem_univ, not_true_eq_false] at hy
  calc
    L₁ v = L₁ (∑ x : X, v x • (Pi.single x (1 : R) : X → R)) := by
      exact congrArg L₁ hv
    _ = ∑ x : X, v x • L₁ (Pi.single x (1 : R)) := by simp only [map_sum, map_smul]
    _ = ∑ x : X, v x • L₂ (Pi.single x (1 : R)) := by simp only [h]
    _ = L₂ (∑ x : X, v x • (Pi.single x (1 : R) : X → R)) := by simp only [map_sum, map_smul]
    _ = L₂ v := by
      exact (congrArg L₂ hv).symm

end JacobianLinearMap

end

end FoxDifferential
