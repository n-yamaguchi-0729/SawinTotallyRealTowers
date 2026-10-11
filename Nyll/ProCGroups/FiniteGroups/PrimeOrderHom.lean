/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Homomorphisms from finite groups of prime order

These elementary group-theoretic facts are shared by the ab-faithfulness
criterion and by Galois-theoretic character arguments.
-/

namespace ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- A homomorphism out of a prime-order group is injective exactly when it is nontrivial. -/
theorem injective_iff_ne_one_of_prime_card
    {B : Type u} {A : Type v} [Group B] [Group A]
    (ρ : B →* A) (hB : Nat.Prime (Nat.card B)) :
    Function.Injective ρ ↔ ρ ≠ 1 := by
  let : Fact (Nat.Prime (Nat.card B)) := ⟨hB⟩
  constructor
  · intro hinj htriv
    have hker : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).2 hinj
    have htop : ρ.ker = ⊤ := MonoidHom.ker_eq_top_iff.2 htriv
    have hcard : Nat.card B = 1 := by
      have hsubsingleton : Subsingleton B := by
        refine ⟨fun x y => ?_⟩
        have hx : x = 1 := by
          have hxmem : x ∈ ρ.ker := htop.symm ▸ Subgroup.mem_top x
          exact (show x ∈ (⊥ : Subgroup B) from hker ▸ hxmem)
        have hy : y = 1 := by
          have hymem : y ∈ ρ.ker := htop.symm ▸ Subgroup.mem_top y
          exact (show y ∈ (⊥ : Subgroup B) from hker ▸ hymem)
        exact hx.trans hy.symm
      let : Subsingleton B := hsubsingleton
      exact Nat.card_unique
    exact hB.ne_one hcard
  · intro hnontrivial
    rcases ρ.ker.eq_bot_or_eq_top_of_prime_card with hbot | htop
    · exact (MonoidHom.ker_eq_bot_iff ρ).1 hbot
    · exact False.elim (hnontrivial (MonoidHom.ker_eq_top_iff.1 htop))

/-- A noninjective homomorphism from a finite group has a prime-order subgroup in its kernel. -/
theorem exists_prime_card_subgroup_le_ker_of_not_injective
    {B : Type u} {A : Type v} [Group B] [Finite B] [Group A]
    (ρ : B →* A) (hρ : ¬ Function.Injective ρ) :
    ∃ C : Subgroup B, Nat.Prime (Nat.card C) ∧ C ≤ ρ.ker := by
  have hcard : Nat.card ρ.ker ≠ 1 := by
    intro hcard
    exact hρ ((MonoidHom.ker_eq_bot_iff ρ).1 ((Subgroup.eq_bot_iff_card ρ.ker).2 hcard))
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ρ.ker) p hpdvd
  let D : Subgroup ρ.ker := Subgroup.zpowers x
  let C : Subgroup B := D.map ρ.ker.subtype
  have hCcard : Nat.card C = p := by
    calc
      Nat.card C = Nat.card D :=
        (Nat.card_congr
          (D.equivMapOfInjective ρ.ker.subtype Subtype.val_injective).toEquiv).symm
      _ = orderOf x := Nat.card_zpowers x
      _ = p := hx
  refine ⟨C, hCcard.symm ▸ hp, ?_⟩
  intro b hb
  obtain ⟨d, hd, hdb⟩ := hb
  exact hdb ▸ d.property

end ProCGroups.FiniteStepSolvableQuotients
