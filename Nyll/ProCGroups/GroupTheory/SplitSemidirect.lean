/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Hom.Basic

/-!
# A split homomorphism as its kernel semidirect product

The section acts on the actual kernel by conjugation. Multiplication of a
kernel element by the image of the section reconstructs the original group.
No commutativity or finiteness assumption is required.
-/

namespace ProCGroups

universe uE uB

variable {E : Type uE} [Group E] {B : Type uB} [Group B]

/-- A section identifies the kernel semidirect product with the original
group, using conjugation by that same section as the action. -/
noncomputable def splitKernelSemidirectMulEquiv
    (α : E →* B) (s : B →* E) (hs : α.comp s = MonoidHom.id B) :
    α.ker ⋊[(MulAut.conjNormal : E →* MulAut α.ker).comp s] B ≃* E := by
  let f : α.ker ⋊[(MulAut.conjNormal : E →* MulAut α.ker).comp s] B →* E :=
    SemidirectProduct.lift α.ker.subtype s (by
      intro b
      apply MonoidHom.ext
      intro a
      change s b * (a : E) * (s b)⁻¹ = s b * (a : E) * (s b)⁻¹
      rfl)
  have hs_apply (b : B) : α (s b) = b := DFunLike.congr_fun hs b
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · apply (injective_iff_map_eq_one f).mpr
    intro x hx
    change (x.left : E) * s x.right = 1 at hx
    have hright : x.right = 1 := by
      have h := congrArg α hx
      rw [map_mul, x.left.property, hs_apply, one_mul, map_one] at h
      exact h
    apply SemidirectProduct.ext
    · apply Subtype.ext
      change (x.left : E) = 1
      rw [hright, map_one, mul_one] at hx
      exact hx
    · exact hright
  · intro e
    let a : α.ker := ⟨e * (s (α e))⁻¹, by
      change α (e * (s (α e))⁻¹) = 1
      rw [map_mul, map_inv, hs_apply, mul_inv_cancel]⟩
    refine ⟨⟨a, α e⟩, ?_⟩
    change e * (s (α e))⁻¹ * s (α e) = e
    rw [mul_assoc, inv_mul_cancel, mul_one]

/-- The equivalence is the actual multiplication map determined by the section. -/
theorem splitKernelSemidirectMulEquiv_apply
    (α : E →* B) (s : B →* E) (hs : α.comp s = MonoidHom.id B)
    (a : α.ker) (b : B) :
    splitKernelSemidirectMulEquiv α s hs ⟨a, b⟩ = (a : E) * s b := by
  rfl

/-- The equivalence intertwines the original epimorphism and the projection
to the second semidirect-product coordinate. -/
theorem splitKernelSemidirectMulEquiv_commutes
    (α : E →* B) (s : B →* E) (hs : α.comp s = MonoidHom.id B)
    (x : α.ker ⋊[(MulAut.conjNormal : E →* MulAut α.ker).comp s] B) :
    α (splitKernelSemidirectMulEquiv α s hs x) = x.right := by
  change α ((x.left : E) * s x.right) = x.right
  rw [map_mul, x.left.property, one_mul]
  exact DFunLike.congr_fun hs x.right

end ProCGroups
