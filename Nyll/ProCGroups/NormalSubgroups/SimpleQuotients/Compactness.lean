/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.NormalSubgroups.SimpleQuotients.FiniteIntersections

/-!
# Compactness for intersections above a simple-quotient kernel

This module upgrades a finite-intersection property for closed normal subgroups of a compact
group to the corresponding arbitrary-intersection property.
-/

namespace ProCGroups.NormalSubgroups

universe u

/--
Compactness step: if the closed normal subgroups satisfying \(M \sqcup K = \top\) are already
stable under finite intersections, then they are stable under arbitrary intersections.
-/
theorem maximal_open_normal_intersections_compactness_step
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (K : Subgroup G) [K.Normal] (hKclosed : IsClosed (K : Set G))
    (𝓜 : Set (Subgroup G))
    (hMclosed : ∀ M ∈ 𝓜, IsClosed (M : Set G))
    (hfinite :
      ∀ S : Set (Subgroup G), S.Finite → S ⊆ 𝓜 → sInf S ⊔ K = ⊤) :
    sInf 𝓜 ⊔ K = ⊤ := by
  rw [eq_top_iff]
  intro g _
  by_cases h𝓜 : 𝓜.Nonempty
  · rcases h𝓜 with ⟨M₀, hM₀⟩
    let coset : Set G := {x | g⁻¹ * x ∈ K}
    let I := {M : Subgroup G // M ∈ 𝓜}
    let F : I → Set G := fun i => (i.1 : Set G) ∩ coset
    have hcosetClosed : IsClosed coset := by
      change IsClosed ((fun x : G => g⁻¹ * x) ⁻¹' (K : Set G))
      exact hKclosed.preimage (continuous_const_mul g⁻¹)
    have hclosed : ∀ i : I, IsClosed (F i) := by
      intro i
      exact (hMclosed i.1 i.2).inter hcosetClosed
    have hfiniteNonempty : ∀ s : Finset I, (⋂ i ∈ s, F i).Nonempty := by
      intro s
      let S : Set (Subgroup G) := (fun i : I => i.1) '' (s : Set _)
      have hSfinite : S.Finite := s.finite_toSet.image _
      have hSsub : S ⊆ 𝓜 := by
        rintro M ⟨i, _hi, rfl⟩
        exact i.2
      have htop : sInf S ⊔ K = ⊤ := hfinite S hSfinite hSsub
      have hgmem : g ∈ sInf S ⊔ K := by
        rw [htop]
        exact Subgroup.mem_top g
      rcases (Subgroup.mem_sup_of_normal_right (s := sInf S) (t := K) (x := g)).1 hgmem with
        ⟨l, hlS, k, hk, hlk⟩
      refine ⟨l, ?_⟩
      simp only [Set.mem_iInter]
      intro i hi
      constructor
      · exact (Subgroup.mem_sInf.mp hlS) i.1 ⟨i, hi, rfl⟩
      · have hg : g = l * k := hlk.symm
        have : g⁻¹ * l = k⁻¹ := by
          rw [hg]
          simp only [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
        change g⁻¹ * l ∈ K
        rw [this]
        exact K.inv_mem hk
    rcases CompactSpace.iInter_nonempty (t := F) hclosed hfiniteNonempty with ⟨x, hx⟩
    have hxall : ∀ i : I, x ∈ F i := by
      simpa [F] using hx
    have hxL : x ∈ sInf 𝓜 := by
      rw [Subgroup.mem_sInf]
      intro M hM
      exact (hxall ⟨M, hM⟩).1
    have hxK : g⁻¹ * x ∈ K := (hxall ⟨M₀, hM₀⟩).2
    have hxmem : x * (g⁻¹ * x)⁻¹ ∈ sInf 𝓜 ⊔ K :=
      Subgroup.mul_mem_sup hxL (K.inv_mem hxK)
    simpa [mul_assoc] using hxmem
  · have h𝓜_empty : 𝓜 = ∅ := Set.not_nonempty_iff_eq_empty.mp h𝓜
    have htop : sInf 𝓜 = ⊤ := by
      rw [h𝓜_empty, sInf_empty]
    simp only [htop, le_top, sup_of_le_left, Subgroup.mem_top]

/--
Maximal open normal subgroups with a fixed nonabelian simple quotient are closed under arbitrary
intersections.
-/
theorem maximal_open_normal_intersections_nonabelian_simple
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (K : Subgroup G) [K.Normal] [IsSimpleGroup (G ⧸ K)]
    (hquotNoncomm : ProCGroups.IsNoncommutativeGroup (G ⧸ K))
    (hKclosed : IsClosed (K : Set G))
    (𝓜 : Set (Subgroup G))
    (hMnormal : ∀ M ∈ 𝓜, M.Normal)
    (hMclosed : ∀ M ∈ 𝓜, IsClosed (M : Set G))
    (hMtop : ∀ M ∈ 𝓜, M ⊔ K = ⊤) :
    sInf 𝓜 ⊔ K = ⊤ :=
  maximal_open_normal_intersections_compactness_step K hKclosed 𝓜 hMclosed
    (fun _S hSfinite hSsub =>
      finite_sInf_sup_eq_top_of_noncomm_simple_quotient K hquotNoncomm hSfinite
        (fun M hM => hMnormal M (hSsub hM))
        (fun M hM => hMtop M (hSsub hM)))

end ProCGroups.NormalSubgroups
