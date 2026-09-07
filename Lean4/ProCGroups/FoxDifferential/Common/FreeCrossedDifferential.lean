import ProCGroups.FoxDifferential.Common.CrossedDifferential
import ProCGroups.FoxDifferential.Common.Jacobian
import Mathlib.GroupTheory.FreeGroup.Basic

set_option autoImplicit false

/-!
# Fox differential: common — free crossed differential

The principal declarations in this module are:

- `freeCrossedHomActionLift`
  The standard semidirect-product lift producing a free crossed homomorphism for an arbitrary
  additive action.
- `freeCrossedHomForAction`
  The free crossed homomorphism with prescribed generator values for a general additive action.
  This is the canonical action-level construction; scalar Fox differentials specialize it via
  `scalarCrossedAction`.
- `freeCrossedHomActionLift_right`
  The free-group component of semidirect multiplication.
- `freeCrossedHomForAction_of`
  The free crossed homomorphism takes each free generator to its prescribed basis value.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

variable {R : Type*} [Semiring R]
variable {A : Type*} [AddCommGroup A] [Module R A]
variable {X : Type u}

section GeneralAction

variable (action : FreeGroup X →* Multiplicative (AddAut A)) (basisValue : X → A)

/-- The standard semidirect-product lift producing a free crossed homomorphism for an arbitrary
additive action. -/
def freeCrossedHomActionLift :
    FreeGroup X →* CrossedSemidirectProduct action :=
  FreeGroup.lift fun x => ⟨Multiplicative.ofAdd (basisValue x), FreeGroup.of x⟩

/-- The free-group component of semidirect multiplication. -/
@[simp]
theorem freeCrossedHomActionLift_right (w : FreeGroup X) :
    (freeCrossedHomActionLift action basisValue w).right = w := by
  induction w using FreeGroup.induction_on with
  | C1 => simp only [freeCrossedHomActionLift, map_one, SemidirectProduct.one_right]
  | of x => simp only [freeCrossedHomActionLift, FreeGroup.lift_apply_of]
  | inv_of x hx => simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, SemidirectProduct.mul_right, hx, hy]

/-- The free crossed homomorphism with prescribed generator values for a general additive
action.  This is the canonical action-level construction; scalar Fox differentials specialize it
via `scalarCrossedAction`. -/
def freeCrossedHomForAction : CrossedHom action :=
  CrossedHom.ofSemidirectMonoidHom
    (freeCrossedHomActionLift action basisValue)
    (freeCrossedHomActionLift_right action basisValue)

/-- The free crossed homomorphism takes each free generator to its prescribed basis value. -/
@[simp]
theorem freeCrossedHomForAction_of (x : X) :
    freeCrossedHomForAction action basisValue (FreeGroup.of x) = basisValue x :=
  by
    simp only [freeCrossedHomForAction, CrossedHom.ofSemidirectMonoidHom_apply,
      freeCrossedHomActionLift,
      FreeGroup.lift_apply_of, toAdd_ofAdd]

/-- A crossed homomorphism on a free group is determined by its values on the free generators,
for an arbitrary additive action. -/
theorem freeCrossedHomForAction_unique
    (delta : CrossedHom action)
    (hbasis : ∀ x : X, delta (FreeGroup.of x) = basisValue x) :
    delta = freeCrossedHomForAction action basisValue := by
  apply CrossedHom.ext
  intro w
  induction w using FreeGroup.induction_on with
  | C1 => rw [CrossedHom.map_one, CrossedHom.map_one]
  | of x => rw [hbasis x, freeCrossedHomForAction_of]
  | inv_of x hx => rw [CrossedHom.map_inv, CrossedHom.map_inv, hx]
  | mul u v hu hv => rw [CrossedHom.map_mul, CrossedHom.map_mul, hu, hv]

/-- General-action crossed homomorphisms on a free group are equivalent to generator-value
assignments. -/
def crossedHomForActionEquivGeneratorValues : CrossedHom action ≃ (X → A) where
  toFun delta x := delta (FreeGroup.of x)
  invFun values := freeCrossedHomForAction action values
  left_inv delta := (freeCrossedHomForAction_unique action
    (fun x => delta (FreeGroup.of x)) delta (by intro x; rfl)).symm
  right_inv values := by
    funext x
    exact freeCrossedHomForAction_of action values x

end GeneralAction

variable (coeff : FreeGroup X →* R) (basisValue : X → A)

/--
The semidirect lift whose left component is the free crossed differential with prescribed
generator values.
-/
def freeCrossedDifferentialWithCoeffLift :
    FreeGroup X →* CrossedSemidirectProduct (scalarCrossedAction (A := A) coeff) :=
  freeCrossedHomActionLift (scalarCrossedAction (A := A) coeff) basisValue

/-- The free crossed differential with coefficient homomorphism `coeff` and prescribed generator
values `basisValue`. -/
def freeCrossedDifferentialWithCoeff (w : FreeGroup X) : A :=
  Multiplicative.toAdd
    (freeCrossedDifferentialWithCoeffLift (A := A) coeff basisValue w).left

/-- The right component of the free crossed-differential lift is the identity on the free group. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffLift_right (w : FreeGroup X) :
    (freeCrossedDifferentialWithCoeffLift (A := A) coeff basisValue w).right = w := by
  exact freeCrossedHomActionLift_right
    (scalarCrossedAction (A := A) coeff) basisValue w

/-- The free crossed differential sends the identity word to zero. -/
@[simp]
theorem freeCrossedDifferentialWithCoeff_one :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue 1 = 0 := by
  change
    freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue 1 = 0
  exact CrossedHom.map_one
    (freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue)

/-- The free crossed differential sends a free generator to its prescribed value. -/
@[simp]
theorem freeCrossedDifferentialWithCoeff_of (x : X) :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue (FreeGroup.of x) =
      basisValue x := by
  change
    freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue
        (FreeGroup.of x) =
      basisValue x
  exact freeCrossedHomForAction_of
    (scalarCrossedAction (A := A) coeff) basisValue x

/-- Product rule for the free crossed differential with arbitrary coefficients. -/
theorem freeCrossedDifferentialWithCoeff_mul (u v : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue (u * v) =
      freeCrossedDifferentialWithCoeff (A := A) coeff basisValue u +
        coeff u • freeCrossedDifferentialWithCoeff (A := A) coeff basisValue v := by
  change
    freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue (u * v) =
      freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue u +
        coeff u •
          freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue v
  exact ScalarCrossedHom.map_mul
    (freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue) u v

/-- Inverse rule for the free crossed differential with arbitrary coefficients. -/
theorem freeCrossedDifferentialWithCoeff_inv (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := A) coeff basisValue w⁻¹ =
      -(coeff w⁻¹ • freeCrossedDifferentialWithCoeff (A := A) coeff basisValue w) := by
  change
    freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue w⁻¹ =
      -(coeff w⁻¹ •
        freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue w)
  exact ScalarCrossedHom.map_inv
    (freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue) w

/--
The free crossed differential with coefficient homomorphism \(\mathrm{coeff}\) and prescribed
generator values \(\mathrm{basisValue}\).
-/
def freeCrossedHomWithCoeff : ScalarCrossedHom coeff A :=
  freeCrossedHomForAction (scalarCrossedAction (A := A) coeff) basisValue

/-- Evaluating the bundled free crossed homomorphism gives the corresponding free crossed
differential. -/
@[simp]
theorem freeCrossedHomWithCoeff_apply (w : FreeGroup X) :
    freeCrossedHomWithCoeff (A := A) coeff basisValue w =
      freeCrossedDifferentialWithCoeff (A := A) coeff basisValue w :=
  rfl

/-- The free crossed differential sends a free generator to its prescribed value. -/
@[simp]
theorem freeCrossedHomWithCoeff_of (x : X) :
    freeCrossedHomWithCoeff (A := A) coeff basisValue (FreeGroup.of x) = basisValue x :=
  freeCrossedDifferentialWithCoeff_of (A := A) coeff basisValue x

/--
Uniqueness of crossed differentials on a free group from their generator values, for an
arbitrary coefficient homomorphism.
-/
theorem freeCrossedHomWithCoeff_unique
    (delta : ScalarCrossedHom coeff A)
    (hbasis : ∀ x : X, delta (FreeGroup.of x) = basisValue x) :
    delta = freeCrossedHomWithCoeff (A := A) coeff basisValue := by
  exact freeCrossedHomForAction_unique
    (scalarCrossedAction (A := A) coeff) basisValue delta hbasis

/--
Existence and uniqueness of crossed differentials on a free group from arbitrary generator
values and an arbitrary coefficient homomorphism.
-/
theorem existsUnique_freeCrossedHomWithCoeff :
    ∃! delta : ScalarCrossedHom coeff A,
      ∀ x : X, delta (FreeGroup.of x) = basisValue x := by
  refine ⟨freeCrossedHomWithCoeff (A := A) coeff basisValue, ?_, ?_⟩
  · exact freeCrossedHomWithCoeff_of (A := A) coeff basisValue
  · intro delta hdelta
    exact freeCrossedHomWithCoeff_unique (A := A) coeff basisValue delta hdelta

/--
Crossed differentials on a free group are equivalent to assignments of values on the free
generators.
-/
def crossedHomEquivGeneratorValues : ScalarCrossedHom coeff A ≃ (X → A) where
  toFun delta := fun x => delta (FreeGroup.of x)
  invFun basisValue := freeCrossedHomWithCoeff (A := A) coeff basisValue
  left_inv delta := by
    exact (freeCrossedHomWithCoeff_unique (A := A) coeff
      (fun x => delta (FreeGroup.of x)) delta (by intro x; rfl)).symm
  right_inv basisValue := by
    funext x
    exact freeCrossedHomWithCoeff_of (A := A) coeff basisValue x

section Coordinates

variable {S : Type*} [Ring S]
variable {B : Type*} [AddCommGroup B] [Module S B]
variable {Y : Type v}
variable [DecidableEq X]

/-- The universal Fox-coordinate crossed differential for an arbitrary coefficient homomorphism
to a ring. -/
def freeCrossedDifferentialWithCoeffCoordinates
    (coeff : FreeGroup X →* S) (w : FreeGroup X) : X → S :=
  freeCrossedDifferentialWithCoeff
    (A := X → S) coeff (fun x => Pi.single x (1 : S)) w

/--
The universal Fox-coordinate crossed differential for an arbitrary coefficient homomorphism to a
ring.
-/
def freeCrossedHomWithCoeffCoordinates
    (coeff : FreeGroup X →* S) : ScalarCrossedHom coeff (X → S) :=
  freeCrossedHomWithCoeff
    (A := X → S) coeff (fun x => Pi.single x (1 : S))

/-- Evaluating the bundled coordinate crossed homomorphism gives the unbundled coordinate
differential. -/
@[simp]
theorem freeCrossedHomWithCoeffCoordinates_apply
    (coeff : FreeGroup X →* S) (w : FreeGroup X) :
    freeCrossedHomWithCoeffCoordinates (X := X) coeff w =
      freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff w :=
  rfl

/-- The coordinate crossed differential sends the identity word to zero. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffCoordinates_one
    (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff (1 : FreeGroup X) = 0 := by
  simp only [freeCrossedDifferentialWithCoeffCoordinates, freeCrossedDifferentialWithCoeff_one]

/-- The coordinate crossed differential sends a generator to the standard coordinate vector. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffCoordinates_of
    (coeff : FreeGroup X →* S) (x : X) :
    freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff (FreeGroup.of x) =
      Pi.single x (1 : S) := by
  simp only [freeCrossedDifferentialWithCoeffCoordinates, freeCrossedDifferentialWithCoeff_of]

/-- The finite linear map evaluating a coordinate vector on prescribed generator values. -/
def freeCrossedDifferentialWithCoeffExpansionLinearMap
    [Fintype X] (basisValue : X → B) : (X → S) →ₗ[S] B where
  toFun v := ∑ x : X, v x • basisValue x
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]

omit [DecidableEq X] in
/-- The coefficient-expansion linear map evaluates `v` as `∑ x, v x • basisValue x`. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffExpansionLinearMap_apply
    [Fintype X] (basisValue : X → B) (v : X → S) :
    freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue v =
      ∑ x : X, v x • basisValue x :=
  rfl

/-- The expansion linear map sends a standard coordinate vector to the corresponding value. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffExpansionLinearMap_single
    [Fintype X] (basisValue : X → B) (x : X) :
    freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue
        (Pi.single x (1 : S)) =
      basisValue x := by
  rw [freeCrossedDifferentialWithCoeffExpansionLinearMap_apply]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_smul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_smul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_smul, IsEmpty.forall_iff]

/-- The Fox-coordinate expansion determined by arbitrary coefficient coordinates. -/
def freeCrossedDifferentialWithCoeffExpansion
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B)
    (w : FreeGroup X) : B :=
  freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue
    (freeCrossedDifferentialWithCoeffCoordinates (X := X) coeff w)

/-- Arbitrary coefficient coordinates determine the Fox-coordinate expansion. -/
def freeCrossedHomWithCoeffExpansion
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) :
    ScalarCrossedHom coeff B :=
  ScalarCrossedHom.mapLinear
    (freeCrossedHomWithCoeffCoordinates (X := X) coeff)
    (freeCrossedDifferentialWithCoeffExpansionLinearMap (X := X) basisValue)

/-- Evaluating the bundled coordinate expansion gives the corresponding unbundled Fox
expansion. -/
@[simp]
theorem freeCrossedHomWithCoeffExpansion_apply
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) (w : FreeGroup X) :
    freeCrossedHomWithCoeffExpansion (X := X) coeff basisValue w =
      freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue w :=
  rfl

/-- The coefficient-coordinate expansion sends each generator to its prescribed value. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffExpansion_of
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) (x : X) :
    freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue (FreeGroup.of x) =
      basisValue x := by
  rw [freeCrossedDifferentialWithCoeffExpansion,
    freeCrossedDifferentialWithCoeffCoordinates_of,
    freeCrossedDifferentialWithCoeffExpansionLinearMap_single]

/-- A free crossed differential is its coefficient-coordinate expansion. -/
theorem freeCrossedDifferentialWithCoeff_eq_expansion
    [Fintype X] (coeff : FreeGroup X →* S) (basisValue : X → B) (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeff (A := B) coeff basisValue w =
      freeCrossedDifferentialWithCoeffExpansion (X := X) coeff basisValue w := by
  have h := freeCrossedHomWithCoeff_unique
    (A := B) coeff basisValue
    (freeCrossedHomWithCoeffExpansion (X := X) coeff basisValue)
    (freeCrossedDifferentialWithCoeffExpansion_of (X := X) coeff basisValue)
  exact congrArg (fun d : ScalarCrossedHom coeff B => d w) h.symm

/--
Abstract Fox chain rule: composing a crossed differential with a free-group homomorphism is the
coordinate expansion using the pulled-back coefficient homomorphism.
-/
theorem freeCrossedHomWithCoeff_comp_expansion
    [Fintype X]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (delta : ScalarCrossedHom coeff B) (w : FreeGroup X) :
    delta (φ w) =
      freeCrossedDifferentialWithCoeffExpansion
        (X := X) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) w := by
  let pulled : ScalarCrossedHom (coeff.comp φ) B :=
    ScalarCrossedHom.compMonoidHom delta φ
  have hunique :
      pulled =
        freeCrossedHomWithCoeff
          (A := B) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) :=
    freeCrossedHomWithCoeff_unique
      (A := B) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x)))
      pulled (by intro x; rfl)
  calc
    delta (φ w) = pulled w := rfl
    _ =
        freeCrossedDifferentialWithCoeff
          (A := B) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) w := by
          exact congrArg (fun d : ScalarCrossedHom (coeff.comp φ) B => d w) hunique
    _ =
        freeCrossedDifferentialWithCoeffExpansion
          (X := X) (coeff.comp φ) (fun x : X => delta (φ (FreeGroup.of x))) w := by
          exact freeCrossedDifferentialWithCoeff_eq_expansion
            (X := X) (B := B) (coeff.comp φ)
            (fun x : X => delta (φ (FreeGroup.of x))) w

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian of a homomorphism of free sources, with coefficients in S. -/
def freeCrossedDifferentialWithCoeffJacobian
    [DecidableEq Y] (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) :
    X → Y → S :=
  fun x => freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ (FreeGroup.of x))

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian of a free-source homomorphism as a matrix. -/
def freeCrossedDifferentialWithCoeffJacobianMatrix
    [DecidableEq Y] (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) :
    Matrix X Y S :=
  foxJacobianMatrix (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ)

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian matrix entry is the corresponding Fox-Jacobian component. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianMatrix_apply
    [DecidableEq Y] (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (x : X) (y : Y) :
    freeCrossedDifferentialWithCoeffJacobianMatrix (X := X) coeff φ x y =
      freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x y :=
  rfl

omit [DecidableEq X] in
/--
The abstract Fox-Jacobian determines a finite linear map between the corresponding free
coefficient modules.
-/
def freeCrossedDifferentialWithCoeffJacobianLinearMap
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) :
    (X → S) →ₗ[S] (Y → S) :=
  foxJacobianLinearMap (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ)

omit [DecidableEq X] in
/--
Evaluation of the linear map associated with the abstract Fox-Jacobian is computed by the
corresponding matrix coefficient formula.
-/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_apply
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (v : X → S) (y : Y) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ v y =
      ∑ x : X, v x * freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x y :=
  rfl

/-- The abstract Fox-Jacobian linear map sends a source basis vector to the corresponding row. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_single
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) (x : X) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ
        (Pi.single x (1 : S)) =
      freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x := by
  exact foxJacobianLinearMap_single
    (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ) x

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian linear map is row-vector multiplication by its matrix. -/
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_eq_vecMul
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y) (v : X → S) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ v =
      Matrix.vecMul v
        (freeCrossedDifferentialWithCoeffJacobianMatrix (X := X) coeff φ) := by
  exact foxJacobianLinearMap_eq_vecMul
    (freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ) v

/-- The abstract Fox-Jacobian of the identity homomorphism is the identity family. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobian_id (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffJacobian
        (X := X) (Y := X) coeff (MonoidHom.id (FreeGroup X)) =
      foxJacobianId (R := S) (X := X) := by
  funext x y
  simp only [freeCrossedDifferentialWithCoeffJacobian, MonoidHom.id_apply,
  freeCrossedDifferentialWithCoeffCoordinates_of, foxJacobianId]

/-- The abstract Fox-Jacobian matrix of the identity homomorphism is the identity matrix. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianMatrix_id (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffJacobianMatrix
        (X := X) (Y := X) coeff (MonoidHom.id (FreeGroup X)) =
      (1 : Matrix X X S) := by
  rw [freeCrossedDifferentialWithCoeffJacobianMatrix,
    freeCrossedDifferentialWithCoeffJacobian_id]
  simp only [foxJacobianMatrix_id]

/-- The abstract Fox-Jacobian linear map of the identity homomorphism is the identity. -/
@[simp]
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_id
    [Fintype X] (coeff : FreeGroup X →* S) :
    freeCrossedDifferentialWithCoeffJacobianLinearMap
        (X := X) (Y := X) coeff (MonoidHom.id (FreeGroup X)) =
      (LinearMap.id : (X → S) →ₗ[S] (X → S)) := by
  rw [freeCrossedDifferentialWithCoeffJacobianLinearMap,
    freeCrossedDifferentialWithCoeffJacobian_id]
  simp only [foxJacobianLinearMap_id]

/-- Abstract Fox chain rule for coordinate vectors, written as a Jacobian linear-map identity. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) =
      freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ
        (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w) := by
  have h :=
    freeCrossedHomWithCoeff_comp_expansion
      (X := X) (Y := Y) (B := Y → S) coeff φ
      (freeCrossedHomWithCoeffCoordinates (X := Y) coeff) w
  calc
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) =
        freeCrossedDifferentialWithCoeffExpansion
          (X := X) (coeff.comp φ)
          (fun x : X =>
            freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff
              (φ (FreeGroup.of x))) w := h
    _ =
        freeCrossedDifferentialWithCoeffJacobianLinearMap (X := X) coeff φ
          (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w) := by
          funext y
          simp only [freeCrossedDifferentialWithCoeffExpansion,
              freeCrossedDifferentialWithCoeffExpansionLinearMap,
  LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
  freeCrossedDifferentialWithCoeffJacobianLinearMap, foxJacobianLinearMap_apply,
  freeCrossedDifferentialWithCoeffJacobian]

/--
Component form of the abstract Fox chain rule: the pushed-forward coordinate is the sum over
source coordinates weighted by the Fox-Jacobian.
-/
theorem freeCrossedDifferentialWithCoeffCoordinates_comp_apply
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) (y : Y) :
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) y =
      ∑ x : X,
        freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w x *
          freeCrossedDifferentialWithCoeffJacobian (X := X) coeff φ x y := by
  exact congrFun
    (freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap
      (X := X) (Y := Y) coeff φ w) y

/-- Abstract Fox chain rule for coordinate vectors, written as matrix multiplication. -/
theorem freeCrossedDifferentialWithCoeffCoordinates_comp_matrix
    [Fintype X] [DecidableEq Y]
    (coeff : FreeGroup Y →* S) (φ : FreeGroup X →* FreeGroup Y)
    (w : FreeGroup X) :
    freeCrossedDifferentialWithCoeffCoordinates (X := Y) coeff (φ w) =
      Matrix.vecMul
        (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w)
        (freeCrossedDifferentialWithCoeffJacobianMatrix (X := X) coeff φ) := by
  rw [freeCrossedDifferentialWithCoeffCoordinates_comp_linearMap]
  exact freeCrossedDifferentialWithCoeffJacobianLinearMap_eq_vecMul
    (X := X) coeff φ
    (freeCrossedDifferentialWithCoeffCoordinates (X := X) (coeff.comp φ) w)

omit [DecidableEq X] in
/--
Component form of the abstract Fox-Jacobian chain rule for a composite of free-group
homomorphisms.
-/
theorem freeCrossedDifferentialWithCoeffJacobian_comp_apply
    {Z : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y)
    (x : X) (z : Z) :
    freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Z) coeff (φ.comp χ) x z =
      ∑ y : Y,
        freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (coeff.comp φ) χ x y *
          freeCrossedDifferentialWithCoeffJacobian (X := Y) (Y := Z) coeff φ y z := by
  simpa [freeCrossedDifferentialWithCoeffJacobian] using
    freeCrossedDifferentialWithCoeffCoordinates_comp_apply
      (X := Y) (Y := Z) coeff φ (χ (FreeGroup.of x)) z

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian chain rule is expressed in family form. -/
theorem freeCrossedDifferentialWithCoeffJacobian_comp
    {Z : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Z) coeff (φ.comp χ) =
      fun x z =>
        ∑ y : Y,
          freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (coeff.comp φ) χ x y *
            freeCrossedDifferentialWithCoeffJacobian (X := Y) (Y := Z) coeff φ y z := by
  funext x z
  exact freeCrossedDifferentialWithCoeffJacobian_comp_apply
    (X := X) (Y := Y) coeff φ χ x z

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian chain rule is expressed in linear-map form. -/
theorem freeCrossedDifferentialWithCoeffJacobianLinearMap_comp
    {Z : Type*} [Fintype X] [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    (freeCrossedDifferentialWithCoeffJacobianLinearMap (X := Y) (Y := Z) coeff φ).comp
        (freeCrossedDifferentialWithCoeffJacobianLinearMap
          (X := X) (Y := Y) (coeff.comp φ) χ) =
      freeCrossedDifferentialWithCoeffJacobianLinearMap
        (X := X) (Y := Z) coeff (φ.comp χ) := by
  change
    (foxJacobianLinearMap
        (freeCrossedDifferentialWithCoeffJacobian (X := Y) (Y := Z) coeff φ)).comp
      (foxJacobianLinearMap
        (freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Y) (coeff.comp φ) χ)) =
    foxJacobianLinearMap
      (freeCrossedDifferentialWithCoeffJacobian (X := X) (Y := Z) coeff (φ.comp χ))
  rw [foxJacobianLinearMap_comp]
  congr
  funext x z
  exact (freeCrossedDifferentialWithCoeffJacobian_comp_apply
    (X := X) (Y := Y) coeff φ χ x z).symm

omit [DecidableEq X] in
/-- The abstract Fox-Jacobian chain rule is expressed in matrix form. -/
theorem freeCrossedDifferentialWithCoeffJacobianMatrix_comp
    {Z : Type*} [Fintype Y] [DecidableEq Y] [DecidableEq Z]
    (coeff : FreeGroup Z →* S)
    (φ : FreeGroup Y →* FreeGroup Z) (χ : FreeGroup X →* FreeGroup Y) :
    freeCrossedDifferentialWithCoeffJacobianMatrix
        (X := X) (Y := Z) coeff (φ.comp χ) =
      freeCrossedDifferentialWithCoeffJacobianMatrix
          (X := X) (Y := Y) (coeff.comp φ) χ *
        freeCrossedDifferentialWithCoeffJacobianMatrix
          (X := Y) (Y := Z) coeff φ := by
  apply Matrix.ext
  intro x z
  simp only [freeCrossedDifferentialWithCoeffJacobianMatrix, foxJacobianMatrix_apply,
  freeCrossedDifferentialWithCoeffJacobian_comp_apply, Matrix.mul_apply]

end Coordinates

end

end FoxDifferential
