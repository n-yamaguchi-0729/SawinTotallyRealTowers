/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Coset.Card

/-!
# Coprimality through a joint group embedding

The inertia group of a compositum embeds in the product of the inertia
groups of the two factors.  This file records the elementary consequence
needed to propagate tameness to the compositum.
-/

noncomputable section

namespace TameAbhyankar.SGA1

/-- If a finite group embeds in a product of two finite groups whose orders
are both prime to `p`, then its order is prime to `p`. -/
theorem card_coprime_of_prod_injective
    {G H J : Type*} [Group G] [Group H] [Group J]
    [Finite G] [Finite H] [Finite J]
    (toH : G →* H) (toJ : G →* J)
    (hinjective : Function.Injective (toH.prod toJ))
    (p : ℕ)
    (hH : Nat.Coprime (Nat.card H) p)
    (hJ : Nat.Coprime (Nat.card J) p) :
    Nat.Coprime (Nat.card G) p := by
  have hdvd : Nat.card G ∣ Nat.card (H × J) :=
    Subgroup.card_dvd_of_injective (toH.prod toJ) hinjective
  have hprod : Nat.Coprime (Nat.card (H × J)) p := by
    simpa only [Nat.card_prod] using hH.mul_left hJ
  exact hprod.of_dvd_left hdvd

end TameAbhyankar.SGA1
