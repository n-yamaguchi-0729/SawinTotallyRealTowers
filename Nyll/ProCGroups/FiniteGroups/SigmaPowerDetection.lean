/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-power detection in finite Sigma groups
-/

namespace ProCGroups.FiniteGroupClass

universe u

/-- An element with an ℓ^s-th root for every allowed prime ℓ and positive s is trivial. -/
theorem eq_one_of_primePower_roots
    {sigma : Set ℕ} {G : Type u} [Group G] [Finite G]
    (hG : FiniteGroupClass.sigmaGroup sigma G) (x : G)
    (hx : ∀ ℓ : ℕ, ℓ ∈ sigma → ℓ.Prime →
      ∀ s : ℕ, 0 < s → ∃ y : G, y ^ (ℓ ^ s) = x) : x = 1 := by
  by_contra hxone
  have ho : orderOf x ≠ 1 := fun h => hxone (orderOf_eq_one_iff.mp h)
  obtain ⟨ℓ, hℓ, hℓo⟩ := Nat.exists_prime_and_dvd ho
  have hℓcard : ℓ ∣ Nat.card G := hℓo.trans (orderOf_dvd_natCard x)
  have hℓsigma : ℓ ∈ sigma := by
    by_contra hnot
    exact hG.2 ℓ hℓ hnot hℓcard
  have hcard : Nat.card G ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hs : 0 < (Nat.card G).factorization ℓ := by
    exact (hℓ.factorization_pos_of_dvd hcard hℓcard)
  obtain ⟨y, hy⟩ := hx ℓ hℓsigma hℓ _ hs
  have hpow : x ^ ((Nat.card G / ℓ ^ (Nat.card G).factorization ℓ)) = 1 := by
    rw [← hy, ← pow_mul]
    rw [Nat.ordProj_mul_ordCompl_eq_self]
    exact pow_card_eq_one'
  exact Nat.not_dvd_ordCompl hℓ hcard
    (hℓo.trans (orderOf_dvd_iff_pow_eq_one.mpr hpow))

end ProCGroups.FiniteGroupClass
