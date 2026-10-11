/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Associated

/-!
# Prime-order quotients of finite abelian groups
-/

namespace ProCGroups.Abelian

/-- A prime divisor of a finite abelian group order gives a cyclic quotient of that order. -/
theorem exists_surjective_prime_character_finite
    {p : ℕ} [Fact p.Prime] {A : Type*} [CommGroup A] [Finite A]
    (hp : p ∣ Nat.card A) :
    ∃ χ : A →* Multiplicative (ZMod p), Function.Surjective χ := by
  classical
  obtain ⟨ι, instι, m, hm, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite A
  have (i : ι) : NeZero (m i) := ⟨ne_of_gt (lt_trans Nat.zero_lt_one (hm i))⟩
  have hcard : Nat.card A = ∏ i : ι, m i := by
    rw [Nat.card_congr e.toEquiv, Nat.card_pi]
    apply Finset.prod_congr rfl
    intro i _hi
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [hcard] at hp
  obtain ⟨i, _, hi⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff m).mp hp
  let ψ : A →* Multiplicative (ZMod (m i)) :=
    (Pi.evalMonoidHom (fun j : ι => Multiplicative (ZMod (m j))) i).comp e.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro a
    refine ⟨e.symm (Function.update 1 i a), ?_⟩
    change e (e.symm (Function.update 1 i a)) i = a
    rw [e.apply_symm_apply, Function.update_self]
  let c : Multiplicative (ZMod (m i)) →* Multiplicative (ZMod p) :=
    (ZMod.castHom hi (ZMod p)).toAddMonoidHom.toMultiplicative
  refine ⟨c.comp ψ, ?_⟩
  exact (ZMod.castHom_surjective hi).comp hψ

end ProCGroups.Abelian
