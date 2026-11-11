/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.Logic.Equiv.Set

/-!
# Intermediate fields under an algebra equivalence

An algebra equivalence of ambient fields induces an order equivalence of
their intermediate-field lattices.  This is the ambient-change step used for
Mathlib's chosen separable closures.
-/

@[expose] public section

noncomputable section

namespace ClassFieldTheory

universe u v w

variable {F : Type u} {L : Type v} {L' : Type w}
  [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']

/-- Map intermediate fields along an algebra equivalence of ambient fields. -/
def intermediateFieldAlgEquivOrderIso (e : L ≃ₐ[F] L') :
    IntermediateField F L ≃o IntermediateField F L' where
  toEquiv := {
    toFun := fun E => E.map e.toAlgHom
    invFun := fun E => E.map e.symm.toAlgHom
    left_inv := by
      intro E
      apply SetLike.coe_injective
      exact e.toEquiv.symm_image_image (E : Set L)
    right_inv := by
      intro E
      apply SetLike.coe_injective
      exact e.toEquiv.image_symm_image (E : Set L')
  }
  map_rel_iff' := by
    intro E G
    change e '' (E : Set L) ⊆ e '' (G : Set L) ↔ (E : Set L) ⊆ G
    exact Set.image_subset_image_iff e.injective

end ClassFieldTheory
