/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.NormalSubgroups.Framework

/-!
# Maximal normal subgroups and simple quotients

This module proves that a proper normal subgroup maximal among normal subgroups yields a simple
quotient.
-/

noncomputable section

open scoped Cardinal

namespace ProCGroups.NormalSubgroups

universe u

/-- A maximal normal subgroup gives a simple quotient. -/
theorem maximal_normal_intersection_simple_quotient
    {G : Type u} [Group G] (M : Subgroup G) [M.Normal]
    (hproper : M ≠ ⊤)
    (hmax : ∀ N : Subgroup G, N.Normal → M < N → N = ⊤) :
    IsSimpleGroup (G ⧸ M) := by
  have hnotTopLe : ¬ (⊤ : Subgroup G) ≤ M := by
    intro hle
    exact hproper (le_antisymm le_top hle)
  rcases IsConcreteLE.not_le_iff_exists.mp hnotTopLe with ⟨g, _hgTop, hgM⟩
  refine
    { exists_pair_ne := ⟨QuotientGroup.mk' M g, 1, ?_⟩
      eq_bot_or_eq_top_of_normal := ?_ }
  · intro hg
    exact hgM ((QuotientGroup.eq_one_iff g).mp (by simpa using hg))
  · intro H hH
    let N : Subgroup G := Subgroup.comap (QuotientGroup.mk' M) H
    have hMN : M ≤ N := by
      dsimp [N]
      exact QuotientGroup.le_comap_mk' M H
    have hNnormal : N.Normal := by
      dsimp [N]
      infer_instance
    by_cases hNM : N = M
    · left
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      dsimp [N] at hNM
      rw [hNM]
      ext x
      simp only [MonoidHom.comap_bot, QuotientGroup.ker_mk']
    · right
      have hMNlt : M < N := lt_of_le_of_ne hMN (by
        intro hMN'
        exact hNM hMN'.symm)
      have hNtop : N = ⊤ := hmax N hNnormal hMNlt
      apply Subgroup.comap_injective (QuotientGroup.mk'_surjective M)
      dsimp [N] at hNtop
      rw [hNtop, Subgroup.comap_top]

end ProCGroups.NormalSubgroups
