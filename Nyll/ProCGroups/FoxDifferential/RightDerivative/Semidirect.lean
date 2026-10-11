/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.GroupRing

/-!
# Fox differential: right derivative — semidirect

The principal declarations in this module are:

- `RightFoxSemidirect`
  The right Fox semidirect product records a group element together with its right-derivative
  coordinate.
- `rightHom`
  The right Fox semidirect construction defines a homomorphism from a right derivation.
- `ext`
  The Fox semidirect construction has the stated component formula.
- `one_left`
  The additive component of the identity semidirect element is zero.
-/

namespace FoxDifferential

noncomputable section

/--
The right Fox semidirect product records a group element together with its right-derivative
coordinate.
-/
structure RightFoxSemidirect (G : Type*) [Group G] where
  /-- The group-ring coordinate, representing the right Fox derivative. -/
  left : FoxDifferential.GroupRing G
  /-- The underlying group element. -/
  right : G

namespace RightFoxSemidirect

variable {G : Type*} [Group G]

/-- The Fox semidirect construction has the stated component formula. -/
@[ext]
theorem ext {x y : RightFoxSemidirect G}
    (hleft : x.left = y.left) (hright : x.right = y.right) : x = y := by
  cases x
  cases y
  simp_all

/-- The unit of the right Fox semidirect product is the pair of identity components. -/
instance instOneRightFoxSemidirect : One (RightFoxSemidirect G) where
  one := ⟨0, 1⟩

/--
Multiplication in the right Fox semidirect product is given by the right action and group
multiplication.
-/
instance instMulRightFoxSemidirect : Mul (RightFoxSemidirect G) where
  mul x y :=
    ⟨x.left * MonoidAlgebra.of ℤ G y.right + y.left, x.right * y.right⟩

/--
Inversion in the right Fox semidirect product is computed from the right action and the inverse
in the base group.
-/
instance instInvRightFoxSemidirect : Inv (RightFoxSemidirect G) where
  inv x :=
    ⟨-x.left * MonoidAlgebra.of ℤ G x.right⁻¹, x.right⁻¹⟩

/-- The additive component of the identity semidirect element is zero. -/
@[simp]
theorem one_left : (1 : RightFoxSemidirect G).left = 0 :=
  rfl

/-- The free-group component of the identity semidirect element is the identity word. -/
@[simp]
theorem one_right : (1 : RightFoxSemidirect G).right = 1 :=
  rfl

/-- The left component of semidirect multiplication is computed by the Fox product rule. -/
@[simp]
theorem mul_left (x y : RightFoxSemidirect G) :
    (x * y).left = x.left * MonoidAlgebra.of ℤ G y.right + y.left :=
  rfl

/-- The right component of semidirect multiplication is the product of right components. -/
@[simp]
theorem mul_right (x y : RightFoxSemidirect G) :
    (x * y).right = x.right * y.right :=
  rfl

/-- The left component of the semidirect inverse is computed by the Fox inverse formula. -/
@[simp]
theorem inv_left (x : RightFoxSemidirect G) :
    x⁻¹.left = -x.left * MonoidAlgebra.of ℤ G x.right⁻¹ :=
  rfl

/-- The right component of the semidirect inverse is the inverse of the right component. -/
@[simp]
theorem inv_right (x : RightFoxSemidirect G) :
    x⁻¹.right = x.right⁻¹ :=
  rfl

/-- The right Fox semidirect product carries the group structure induced by its right action. -/
instance instGroupRightFoxSemidirect : Group (RightFoxSemidirect G) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc x y z := by
    apply RightFoxSemidirect.ext
    · simp only [mul_left, mul_right, map_mul, add_mul, mul_assoc, add_assoc]
    · simp only [mul_right, mul_assoc]
  one_mul x := by
    apply RightFoxSemidirect.ext
    · simp only [mul_left, one_left, MonoidAlgebra.of_apply, zero_mul, zero_add]
    · simp only [mul_right, one_right, one_mul]
  mul_one x := by
    apply RightFoxSemidirect.ext
    · simp only [mul_left, one_right, map_one, one_left, add_zero, mul_one]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel x := by
    apply RightFoxSemidirect.ext
    · simp only [mul_left, inv_left]
      rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one,
        neg_add_cancel, one_left]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

/-- The right Fox semidirect construction defines a homomorphism from a right derivation. -/
def rightHom : RightFoxSemidirect G →* G where
  toFun x := x.right
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The right projection homomorphism of a Fox semidirect product returns its right coordinate. -/
@[simp]
theorem rightHom_apply (x : RightFoxSemidirect G) :
    rightHom x = x.right :=
  rfl

end RightFoxSemidirect

end

end FoxDifferential
