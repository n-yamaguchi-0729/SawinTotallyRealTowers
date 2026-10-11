/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The cyclic group argument in Abhyankar's lemma

This file isolates the finite-group calculation in the proof of SGA 1,
Expose X, Lemma 3.6.  A cyclic group embedded in a product of two cyclic
groups has order dividing the order of the second factor when the order of
the first factor already divides it.  Consequently, a surjective projection
to the second factor is an isomorphism.
-/

noncomputable section

namespace TameAbhyankar.SGA1

variable {M G H : Type*}
variable [Group M] [Group G] [Group H]
variable [Finite M] [Finite H]
variable [IsCyclic M] [IsCyclic G]

/-- The group-theoretic order argument in the proof of tame Abhyankar.

If `M` embeds in `G x H`, its projection to `H` is surjective, and
`|G|` divides `|H|`, then the projection `M -> H` is injective. -/
theorem cyclic_right_projection_injective_of_card_dvd
    (toLeft : M →* G) (toRight : M →* H)
    (hpair : Function.Injective (toLeft.prod toRight))
    (hright : Function.Surjective toRight)
    (hcard : Nat.card G ∣ Nat.card H) :
    Function.Injective toRight := by
  have hpowG : ∀ g : G, g ^ Nat.card H = 1 := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    rw [IsCyclic.exponent_eq_card]
    exact hcard
  have hpowH : ∀ h : H, h ^ Nat.card H = 1 := by
    intro h
    exact pow_card_eq_one'
  have hpowM : ∀ m : M, m ^ Nat.card H = 1 := by
    intro m
    apply hpair
    apply Prod.ext
    · change toLeft (m ^ Nat.card H) = toLeft 1
      rw [MonoidHom.map_pow, hpowG, map_one]
    · change toRight (m ^ Nat.card H) = toRight 1
      rw [MonoidHom.map_pow, hpowH, map_one]
  have hM_dvd_H : Nat.card M ∣ Nat.card H := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpowM
  have hM_le_H : Nat.card M ≤ Nat.card H :=
    Nat.le_of_dvd Nat.card_pos hM_dvd_H
  have hH_le_M : Nat.card H ≤ Nat.card M :=
    Nat.card_le_card_of_surjective toRight hright
  have hcard_eq : Nat.card M = Nat.card H :=
    le_antisymm hM_le_H hH_le_M
  exact ((Nat.bijective_iff_surjective_and_card toRight).2
    ⟨hright, hcard_eq⟩).1

/-- Under the hypotheses of the cyclic Abhyankar argument, the right
projection is an isomorphism on the underlying finite groups. -/
theorem cyclic_right_projection_bijective_of_card_dvd
    (toLeft : M →* G) (toRight : M →* H)
    (hpair : Function.Injective (toLeft.prod toRight))
    (hright : Function.Surjective toRight)
    (hcard : Nat.card G ∣ Nat.card H) :
    Function.Bijective toRight :=
  ⟨cyclic_right_projection_injective_of_card_dvd
      toLeft toRight hpair hright hcard,
    hright⟩

/-- Equivalently, the relative group occurring as the kernel of the right
projection is trivial. -/
theorem cyclic_right_projection_ker_eq_bot_of_card_dvd
    (toLeft : M →* G) (toRight : M →* H)
    (hpair : Function.Injective (toLeft.prod toRight))
    (hright : Function.Surjective toRight)
    (hcard : Nat.card G ∣ Nat.card H) :
    MonoidHom.ker toRight = ⊥ :=
  (MonoidHom.ker_eq_bot_iff toRight).mpr
    (cyclic_right_projection_injective_of_card_dvd
      toLeft toRight hpair hright hcard)

end TameAbhyankar.SGA1
