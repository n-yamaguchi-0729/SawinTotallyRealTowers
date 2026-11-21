/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.GroupTheory.Index
public import Mathlib.SetTheory.Cardinal.Finite

/-! # Size bounds in finite exact sequences -/

@[expose] public section

namespace AddMonoidHom

/-- If the kernel at the middle group is contained in the incoming image,
the middle group is finite and its order is at most the product of the outer orders. -/
theorem finite_natCard_le_mul_of_ker_le_range
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) (h : g.ker ≤ f.range) [Finite A] [Finite C] :
    Finite B ∧ Nat.card B ≤ Nat.card A * Nat.card C := by
  have : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Finite g.ker := Finite.of_injective
    (AddSubgroup.inclusion h) (AddSubgroup.inclusion_injective h)
  have hFinite : Finite B := g.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩
  have hKer : Nat.card g.ker ≤ Nat.card A :=
    (Nat.card_le_card_of_injective (AddSubgroup.inclusion h)
      (AddSubgroup.inclusion_injective h)).trans
      (Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hRange : Nat.card g.range ≤ Nat.card C :=
    Nat.card_le_card_of_injective (fun x : g.range ↦ (x : C)) Subtype.val_injective
  refine ⟨hFinite, ?_⟩
  rw [← g.ker.card_mul_index, AddSubgroup.index_ker]
  exact Nat.mul_le_mul hKer hRange

end AddMonoidHom
