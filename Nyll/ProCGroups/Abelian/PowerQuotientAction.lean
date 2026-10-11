/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Automorphism actions on quotients by powers

Multiplicative automorphisms preserve the subgroup of powers and induce
automorphisms of the corresponding quotient, with explicit evaluation.
-/

namespace ProCGroups.Abelian

variable {A : Type*} [CommGroup A]

/-- Multiplicative automorphisms preserve the subgroup of nth powers. -/
theorem map_powerRange (n : ℕ) (e : MulAut A) :
    ((powMonoidHom (α := A) n).range).map e.toMonoidHom =
      (powMonoidHom (α := A) n).range := by
  apply le_antisymm
  · rintro x ⟨y, ⟨a, rfl⟩, rfl⟩
    exact ⟨e a, (map_pow e a n).symm⟩
  · rintro x ⟨a, rfl⟩
    refine ⟨(e.symm a)^n, ⟨e.symm a, rfl⟩, ?_⟩
    change e ((e.symm a)^n) = a^n
    rw [map_pow, MulEquiv.apply_symm_apply]

/-- The action of automorphisms on the quotient by nth powers. -/
noncomputable def powerQuotientAction (n : ℕ) :
    MulAut A →* MulAut (A ⧸ (powMonoidHom (α := A) n).range) where
  toFun e := QuotientGroup.congr _ _ e (map_powerRange n e)
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom (α := A) n).range x
    rfl
  map_mul' e f := by
    apply MulEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (powMonoidHom (α := A) n).range x
    rfl

/-- The quotient automorphism evaluates by applying the original automorphism. -/
theorem powerQuotientAction_mk (n : ℕ) (e : MulAut A) (a : A) :
    powerQuotientAction n e (QuotientGroup.mk' (powMonoidHom (α := A) n).range a) =
      QuotientGroup.mk' (powMonoidHom (α := A) n).range (e a) := rfl

end ProCGroups.Abelian
