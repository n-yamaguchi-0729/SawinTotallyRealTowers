/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.NormalSubgroups.Framework

/-!
# Algebraic properties of simple quotients

This module translates simplicity of `G ⧸ K` into a dichotomy for normal subgroups above `K` and
derives the intersection property needed for noncommutative simple quotients.
-/

namespace ProCGroups.NormalSubgroups

universe u

/--
If \(G/K\) is simple, every normal subgroup of \(G\) containing \(K\) is either \(K\) or all of
\(G\). This is the correspondence theorem form of the simple-quotient dichotomy.
-/
theorem normal_subgroup_eq_kernel_or_top_of_simple_quotient
    {G : Type u} [Group G] (K L : Subgroup G) [K.Normal] (hL : L.Normal)
    [IsSimpleGroup (G ⧸ K)] (hKL : K ≤ L) :
    L = K ∨ L = ⊤ := by
  let qL : Subgroup (G ⧸ K) := Subgroup.map (QuotientGroup.mk' K) L
  have hqLnormal : qL.Normal := inferInstance
  rcases hqLnormal.eq_bot_or_eq_top with hbot | htop
  · left
    apply le_antisymm
    · have hLK : L ≤ K := by
        have hker : L ≤ (QuotientGroup.mk' K).ker :=
          (Subgroup.map_eq_bot_iff L).mp hbot
        simpa [QuotientGroup.ker_mk'] using hker
      exact hLK
    · exact hKL
  · right
    have hcomap : Subgroup.comap (QuotientGroup.mk' K) qL = L := by
      dsimp [qL]
      rw [QuotientGroup.comap_map_mk']
      exact sup_of_le_right hKL
    rw [← hcomap, htop]
    simp only [Subgroup.comap_top]

/--
If subgroups above \(K\) satisfy the two-point dichotomy induced by a simple noncommutative
quotient, then two normal subgroups whose products with \(K\) equal \(G\) retain that property
after intersection.
-/
theorem inf_sup_eq_top_of_simple_quotient_dichotomy
    {G : Type u} [Group G] (K M N : Subgroup G) [K.Normal] [M.Normal] [N.Normal]
    (hsimple : ∀ L : Subgroup G, L.Normal → K ≤ L → L = K ∨ L = ⊤)
    (hquotNoncomm : ProCGroups.IsNoncommutativeGroup (G ⧸ K))
    (hMK : M ⊔ K = ⊤) (hNK : N ⊔ K = ⊤) :
    M ⊓ N ⊔ K = ⊤ := by
  let L : Subgroup G := M ⊓ N ⊔ K
  have hLnormal : L.Normal := inferInstance
  have hKleL : K ≤ L := le_sup_right
  rcases hsimple L hLnormal hKleL with hLK | hLtop
  · exfalso
    have hMNK : ⁅M, N⁆ ≤ K := by
      exact (Subgroup.commutator_le_inf M N).trans ((le_sup_left : M ⊓ N ≤ L).trans_eq hLK)
    have hmapK : Subgroup.map (QuotientGroup.mk' K) K = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hmapM : Subgroup.map (QuotientGroup.mk' K) M = ⊤ := by
      have hmapSup : Subgroup.map (QuotientGroup.mk' K) (M ⊔ K) = ⊤ := by
        rw [hMK]
        exact Subgroup.map_top_of_surjective (QuotientGroup.mk' K)
          (QuotientGroup.mk'_surjective K)
      rw [Subgroup.map_sup, hmapK, sup_bot_eq] at hmapSup
      exact hmapSup
    have hmapN : Subgroup.map (QuotientGroup.mk' K) N = ⊤ := by
      have hmapSup : Subgroup.map (QuotientGroup.mk' K) (N ⊔ K) = ⊤ := by
        rw [hNK]
        exact Subgroup.map_top_of_surjective (QuotientGroup.mk' K)
          (QuotientGroup.mk'_surjective K)
      rw [Subgroup.map_sup, hmapK, sup_bot_eq] at hmapSup
      exact hmapSup
    have hcommBot : commutator (G ⧸ K) = ⊥ := by
      rw [commutator_def]
      nth_rewrite 1 [← hmapM]
      nth_rewrite 1 [← hmapN]
      rw [← Subgroup.map_commutator]
      apply (Subgroup.map_eq_bot_iff ⁅M, N⁆).2
      simpa [QuotientGroup.ker_mk'] using hMNK
    exact hquotNoncomm hcommBot
  · exact hLtop

/-- Algebraic core with the simple quotient written directly. -/
theorem inf_sup_eq_top_of_noncomm_simple_quotient
    {G : Type u} [Group G] (K M N : Subgroup G) [K.Normal] [M.Normal] [N.Normal]
    [IsSimpleGroup (G ⧸ K)]
    (hquotNoncomm : ProCGroups.IsNoncommutativeGroup (G ⧸ K))
    (hMK : M ⊔ K = ⊤) (hNK : N ⊔ K = ⊤) :
    M ⊓ N ⊔ K = ⊤ :=
  inf_sup_eq_top_of_simple_quotient_dichotomy K M N
    (fun L hL hKL => normal_subgroup_eq_kernel_or_top_of_simple_quotient K L hL hKL)
    hquotNoncomm hMK hNK

end ProCGroups.NormalSubgroups
