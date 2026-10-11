/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.GroupTheory.Sylow

/-!
# Lifting elements of finite p-group quotients

A surjection from a finite group onto a p-group admits lifts of p-power
order for every element of the quotient.
-/

namespace ProCGroups

/-- Every element of a finite p-group quotient has a lift of p-power order. -/
theorem exists_prime_power_order_lift_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G]
    (p : ℕ) [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hH : IsPGroup p H) (y : H) :
    ∃ x : G, f x = y ∧ ∃ n : ℕ, x ^ (p ^ n) = 1 := by
  classical
  let P : Sylow p G := Classical.choice Sylow.nonempty
  have htop : (P.mapSurjective hf : Subgroup H) = ⊤ :=
    ((P.mapSurjective hf).is_maximal' (hH.to_subgroup ⊤) le_top).symm
  have hy : y ∈ (P : Subgroup G).map f := by
    change y ∈ (P.mapSurjective hf : Subgroup H)
    rw [htop]
    exact Subgroup.mem_top y
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨n, hn⟩ := P.isPGroup' ⟨x, hx⟩
  exact ⟨x, hxy, n, congrArg (fun z : P => (z : G)) hn⟩

end ProCGroups
