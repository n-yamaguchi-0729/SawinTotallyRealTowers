import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.Core
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.FreeGroup.Fundamental

set_option autoImplicit false

/-!
# Fox differential: completed — semidirect

The principal declarations in this module are:

- `ZCCompletedFoxSemidirect`
  The completed Fox semidirect target `Z_C[[H]]^X ⋊ H`.
- `rightMonoidHom`
  The right projection from the completed Fox semidirect product to the target group.
- `ext`
  Extensionality for completed Fox semidirect elements.
- `one_left`
  The left component of the identity semidirect element is zero.
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

variable (C : ProCGroups.FiniteGroupClass.{v})
variable (X : Type u) [DecidableEq X]
variable (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

omit [DecidableEq X] in
/-- The completed Fox semidirect target `Z_C[[H]]^X ⋊ H`. -/
structure ZCCompletedFoxSemidirect where
  /-- The completed Fox-coordinate component. -/
  left : ZCFreeFoxCoordinates C (X := X) (H := H)
  /-- The target group component. -/
  right : H

namespace ZCCompletedFoxSemidirect

omit [DecidableEq X] in
/-- Extensionality for completed Fox semidirect elements. -/
@[ext]
theorem ext {a b : ZCCompletedFoxSemidirect C X H}
    (hleft : a.left = b.left) (hright : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

/-- Identity element of the completed Fox semidirect product. -/
instance instOneZCCompletedFoxSemidirect : One (ZCCompletedFoxSemidirect C X H) where
  one := ⟨0, 1⟩

/-- Multiplication in the completed Fox semidirect product. -/
instance instMulZCCompletedFoxSemidirect : Mul (ZCCompletedFoxSemidirect C X H) where
  mul a b :=
    ⟨a.left + zcGroupLike C H a.right • b.left, a.right * b.right⟩

/-- Inversion in the completed Fox semidirect product. -/
instance instInvZCCompletedFoxSemidirect : Inv (ZCCompletedFoxSemidirect C X H) where
  inv a :=
    ⟨-(zcGroupLike C H a.right⁻¹ • a.left), a.right⁻¹⟩

omit [DecidableEq X] in
/-- The left component of the identity semidirect element is zero. -/
@[simp]
theorem one_left :
    (1 : ZCCompletedFoxSemidirect C X H).left = 0 :=
  rfl

omit [DecidableEq X] in
/-- The right component of the identity semidirect element is the group identity. -/
@[simp]
theorem one_right :
    (1 : ZCCompletedFoxSemidirect C X H).right = 1 :=
  rfl

omit [DecidableEq X] in
/-- The left component of semidirect multiplication. -/
@[simp]
theorem mul_left (a b : ZCCompletedFoxSemidirect C X H) :
    (a * b).left = a.left + zcGroupLike C H a.right • b.left :=
  rfl

omit [DecidableEq X] in
/-- The right component of semidirect multiplication. -/
@[simp]
theorem mul_right (a b : ZCCompletedFoxSemidirect C X H) :
    (a * b).right = a.right * b.right :=
  rfl

omit [DecidableEq X] in
/-- The left component of semidirect inversion. -/
@[simp]
theorem inv_left (a : ZCCompletedFoxSemidirect C X H) :
    a⁻¹.left = -(zcGroupLike C H a.right⁻¹ • a.left) :=
  rfl

omit [DecidableEq X] in
/-- The right component of semidirect inversion. -/
@[simp]
theorem inv_right (a : ZCCompletedFoxSemidirect C X H) :
    a⁻¹.right = a.right⁻¹ :=
  rfl

/-- Group structure on the completed Fox semidirect product. -/
instance instGroupZCCompletedFoxSemidirect : Group (ZCCompletedFoxSemidirect C X H) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    ext
    · simp only [mul_left, mul_right, map_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_assoc,
  zcCompletedGroupAlgebraProjection_add, zcCompletedGroupAlgebraProjection_mul,
  zcCompletedGroupAlgebraProjection_groupLike, MonoidAlgebra.coeff_add, smul_add, smul_smul]
    · simp only [mul_right, mul_assoc]
  one_mul a := by
    ext
    · simp only [mul_left, one_left, one_right, map_one, one_smul, Pi.add_apply, Pi.zero_apply,
        zero_add]
    · simp only [mul_right, one_right, one_mul]
  mul_one a := by
    ext
    · simp only [mul_left, one_left, smul_zero, Pi.add_apply, Pi.zero_apply, add_zero]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel a := by
    ext
    · simp only [mul_left, inv_left, inv_right, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul,
  neg_add_cancel, zcCompletedGroupAlgebraProjection_zero, Pi.zero_apply, one_left]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

omit [DecidableEq X] in
/-- The right projection from the completed Fox semidirect product to the target group. -/
def rightMonoidHom : ZCCompletedFoxSemidirect C X H →* H where
  toFun a := a.right
  map_one' := rfl
  map_mul' _ _ := rfl

omit [DecidableEq X] in
/-- Projection to the right factor of the completed Fox semidirect product returns its stored
group element. -/
@[simp]
theorem rightMonoidHom_apply (a : ZCCompletedFoxSemidirect C X H) :
    rightMonoidHom C X H a = a.right :=
  rfl

end ZCCompletedFoxSemidirect

section Lift

variable {X H}

/-- The completed Fox semidirect lift of a free group homomorphism. -/
def zcCompletedFoxSemidirectLift (ψ : FreeGroup X →* H) :
    FreeGroup X →* ZCCompletedFoxSemidirect C X H :=
  FreeGroup.lift fun x =>
    { left := Pi.single x (1 : ZCCompletedGroupAlgebra C H)
      right := ψ (FreeGroup.of x) }

/-- The right component of the completed Fox semidirect lift is `ψ`. -/
@[simp]
theorem zcCompletedFoxSemidirectLift_right
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    (zcCompletedFoxSemidirectLift C ψ w).right = ψ w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [zcCompletedFoxSemidirectLift, map_one, ZCCompletedFoxSemidirect.one_right]
  | of x =>
      simp only [zcCompletedFoxSemidirectLift, FreeGroup.lift_apply_of]
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul u v hu hv =>
      simp only [map_mul, ZCCompletedFoxSemidirect.mul_right, hu, hv]

/-- The left component of the completed Fox semidirect lift. -/
def zcCompletedFoxSemidirectDerivativeVector
    (ψ : FreeGroup X →* H) :
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)) where
  toFun w := (zcCompletedFoxSemidirectLift C ψ w).left
  map_mul' u v := by
    simp only [scalarCrossedAction_apply, map_mul, ZCCompletedFoxSemidirect.mul_left,
      zcCompletedFoxSemidirectLift_right,
      zcCompletedGroupAlgebraScalar_apply]

/-- The completed semidirect derivative vector sends a free generator to the coordinate basis
vector. -/
@[simp]
theorem zcCompletedFoxSemidirectDerivativeVector_of
    (ψ : FreeGroup X →* H) (x : X) :
    zcCompletedFoxSemidirectDerivativeVector C ψ (FreeGroup.of x) =
      Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
  change (zcCompletedFoxSemidirectLift C ψ (FreeGroup.of x)).left =
    Pi.single x (1 : ZCCompletedGroupAlgebra C H)
  simp only [zcCompletedFoxSemidirectLift, FreeGroup.lift_apply_of]

/-- The completed semidirect derivative vector is the completed free-group Fox derivative
vector. -/
theorem zcCompletedFoxSemidirectDerivativeVector_eq
    (ψ : FreeGroup X →* H) :
    zcCompletedFoxSemidirectDerivativeVector C ψ =
      zcFreeGroupFoxDerivativeVector C ψ := by
  exact zcFreeGroupFoxDerivativeVector_unique C ψ
    (zcCompletedFoxSemidirectDerivativeVector C ψ)
    (zcCompletedFoxSemidirectDerivativeVector_of C ψ)

/-- The completed semidirect lift stores the completed Fox derivative vector and the target
homomorphism. -/
theorem zcCompletedFoxSemidirectLift_eq
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcCompletedFoxSemidirectLift C ψ w =
      { left := zcFreeGroupFoxDerivativeVector C ψ w
        right := ψ w } := by
  apply ZCCompletedFoxSemidirect.ext
  · rw [← zcCompletedFoxSemidirectDerivativeVector_eq]
    rfl
  · exact zcCompletedFoxSemidirectLift_right C ψ w

omit [DecidableEq X] in
/-- The left component of a semidirect homomorphism with prescribed right component, bundled
as a completed crossed homomorphism. -/
def zcCompletedFoxSemidirectLiftLeftCrossedHom
    (ψ : FreeGroup X →* H)
    (φ : FreeGroup X →* ZCCompletedFoxSemidirect C X H)
    (hright : ∀ w : FreeGroup X, (φ w).right = ψ w) :
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCFreeFoxCoordinates C (X := X) (H := H)) where
  toFun w := (φ w).left
  map_mul' u v := by
    have h := congrArg ZCCompletedFoxSemidirect.left (map_mul φ u v)
    change (φ (u * v)).left =
      (φ u).left + zcCompletedGroupAlgebraScalar C ψ u • (φ v).left
    rw [h]
    simp only [ZCCompletedFoxSemidirect.mul_left, hright u,
      zcCompletedGroupAlgebraScalar_apply]

/-- Uniqueness of the completed semidirect lift with prescribed right component and generator
coordinate values. -/
theorem zcCompletedFoxSemidirectLift_unique
    (ψ : FreeGroup X →* H)
    (φ : FreeGroup X →* ZCCompletedFoxSemidirect C X H)
    (hright : ∀ w : FreeGroup X, (φ w).right = ψ w)
    (hbasis :
      ∀ x : X, (φ (FreeGroup.of x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H)) :
    φ = zcCompletedFoxSemidirectLift C ψ := by
  let delta :=
    zcCompletedFoxSemidirectLiftLeftCrossedHom C ψ φ hright
  have hdelta_eq : delta = zcFreeGroupFoxDerivativeVector C ψ :=
    zcFreeGroupFoxDerivativeVector_unique C ψ delta hbasis
  apply MonoidHom.ext
  intro w
  apply ZCCompletedFoxSemidirect.ext
  · change delta w = zcCompletedFoxSemidirectDerivativeVector C ψ w
    rw [hdelta_eq, zcCompletedFoxSemidirectDerivativeVector_eq]
  · rw [hright w, zcCompletedFoxSemidirectLift_right]

/-- Existence and uniqueness theorem for the completed semidirect lift. -/
theorem existsUnique_zcCompletedFoxSemidirectLift
    (ψ : FreeGroup X →* H) :
    ∃! φ : FreeGroup X →* ZCCompletedFoxSemidirect C X H,
      (∀ w : FreeGroup X, (φ w).right = ψ w) ∧
        ∀ x : X, (φ (FreeGroup.of x)).left =
          Pi.single x (1 : ZCCompletedGroupAlgebra C H) := by
  refine ⟨zcCompletedFoxSemidirectLift C ψ, ?_, ?_⟩
  · exact ⟨zcCompletedFoxSemidirectLift_right C ψ,
      zcCompletedFoxSemidirectDerivativeVector_of C ψ⟩
  · intro φ hφ
    exact zcCompletedFoxSemidirectLift_unique C ψ φ hφ.1 hφ.2

section FiniteBasis

variable [Fintype X]

/-- Boundary-map form of the completed Fox fundamental formula for the semidirect derivative
vector. -/
theorem zcCompletedFoxSemidirectDerivativeVector_foxBoundary
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcFreeGroupFoxBoundary C ψ (zcCompletedFoxSemidirectDerivativeVector C ψ w) =
      zcCompletedGroupAlgebraBoundary C ψ w := by
  exact zcFreeGroupFoxBoundary_of_crossedHom C ψ
    (zcCompletedFoxSemidirectDerivativeVector C ψ)
    (zcCompletedFoxSemidirectDerivativeVector_of C ψ) w

/-- Completed Fox-Euler formula using the left component of the semidirect lift:
`[ψ(w)] - 1 = ∑ i, φ(w)_i * ([ψ(x_i)] - 1)`. -/
theorem zcCompletedFoxSemidirectLift_euler_formula
    (ψ : FreeGroup X →* H) (w : FreeGroup X) :
    zcGroupLike C H (ψ w) - 1 =
      ∑ i : X,
        (zcCompletedFoxSemidirectLift C ψ w).left i *
          (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  exact zcFreeGroupFoxDerivative_euler_formula_of_crossedHom C ψ
    (zcCompletedFoxSemidirectDerivativeVector C ψ)
    (zcCompletedFoxSemidirectDerivativeVector_of C ψ) w

/-- Conditional semidirect Fox boundary formula.  Any semidirect lift with right component `ψ`
and standard generator coordinates satisfies the completed Fox boundary formula. -/
theorem zcCompletedFoxSemidirectLift_foxBoundary_of_generatorValues
    (ψ : FreeGroup X →* H)
    (φ : FreeGroup X →* ZCCompletedFoxSemidirect C X H)
    (hright : ∀ w : FreeGroup X, (φ w).right = ψ w)
    (hbasis :
      ∀ x : X, (φ (FreeGroup.of x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcFreeGroupFoxBoundary C ψ (φ w).left =
      zcCompletedGroupAlgebraBoundary C ψ w := by
  exact zcFreeGroupFoxBoundary_of_crossedHom C ψ
    (zcCompletedFoxSemidirectLiftLeftCrossedHom C ψ φ hright)
    hbasis w

/-- Conditional semidirect Fox-Euler formula.  The left component of any semidirect lift with
right component `ψ` and standard generator coordinates gives the completed Fox-Euler sum. -/
theorem zcCompletedFoxSemidirectLift_euler_formula_of_generatorValues
    (ψ : FreeGroup X →* H)
    (φ : FreeGroup X →* ZCCompletedFoxSemidirect C X H)
    (hright : ∀ w : FreeGroup X, (φ w).right = ψ w)
    (hbasis :
      ∀ x : X, (φ (FreeGroup.of x)).left =
        Pi.single x (1 : ZCCompletedGroupAlgebra C H))
    (w : FreeGroup X) :
    zcGroupLike C H (ψ w) - 1 =
      ∑ i : X,
        (φ w).left i * (zcGroupLike C H (ψ (FreeGroup.of i)) - 1) := by
  exact zcFreeGroupFoxDerivative_euler_formula_of_crossedHom C ψ
    (zcCompletedFoxSemidirectLiftLeftCrossedHom C ψ φ hright)
    hbasis w

end FiniteBasis

end Lift

end

end FoxDifferential
