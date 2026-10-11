/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.SemidirectProduct

/-!
# Kernels and subgroup preimages in a semidirect product

The actual right-projection kernel is its left factor. The preimage of a
subgroup of the right factor is the semidirect product with the restricted
action. Both identifications preserve the displayed coordinates.
-/

namespace ProCGroups

universe uA uQ

variable {A : Type uA} [Group A] {Q : Type uQ} [Group Q]

/-- The actual kernel of the right projection is the left factor. -/
def semidirectRightKernelEquiv (φ : Q →* MulAut A) :
    (SemidirectProduct.rightHom : A ⋊[φ] Q →* Q).ker ≃* A where
  toFun x := (x : A ⋊[φ] Q).left
  invFun a := ⟨SemidirectProduct.inl a, SemidirectProduct.rightHom_inl a⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · rfl
    · exact x.property.symm
  right_inv _ := rfl
  map_mul' x y := by
    change (x : A ⋊[φ] Q).left * φ (x : A ⋊[φ] Q).right
      (y : A ⋊[φ] Q).left = (x : A ⋊[φ] Q).left * (y : A ⋊[φ] Q).left
    have hx : (x : A ⋊[φ] Q).right = 1 := x.property
    rw [hx, map_one, MulAut.one_apply]

/-- The preimage of a subgroup under the right projection has exactly the
restricted semidirect-product action. -/
def semidirectRightPreimageEquiv (φ : Q →* MulAut A) (J : Subgroup Q) :
    J.comap (SemidirectProduct.rightHom : A ⋊[φ] Q →* Q) ≃*
      A ⋊[φ.comp J.subtype] J where
  toFun x := ⟨(x : A ⋊[φ] Q).left, ⟨(x : A ⋊[φ] Q).right, x.property⟩⟩
  invFun x := ⟨⟨x.left, x.right⟩, x.right.property⟩
  left_inv x := by
    apply Subtype.ext
    apply SemidirectProduct.ext <;> rfl
  right_inv x := by
    apply SemidirectProduct.ext <;> rfl
  map_mul' x y := by
    apply SemidirectProduct.ext <;> rfl

end ProCGroups
