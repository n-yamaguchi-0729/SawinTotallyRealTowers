/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ProCGroups.Profinite.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# Central elements from profinite quotient lifts

Compatible finite-quotient central lifts that survive a fixed open quotient
yield a nonidentity element of the profinite center.
-/

namespace ProCGroups.ProfiniteGrp

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Central elements in every finite quotient, each surviving a fixed open
quotient, yield a nonidentity element of the actual profinite center. -/
theorem exists_ne_one_mem_center_of_quotient_central_lifts
    (M : OpenNormalSubgroup G)
    (hlift : ∀ N : OpenNormalSubgroup G, ∃ z : G, z ∉ (M : Subgroup G) ∧
      ∀ g : G, (g * z) * (z * g)⁻¹ ∈ (N : Subgroup G)) :
    ∃ z : G, z ∈ Subgroup.center G ∧ z ≠ 1 := by
  classical
  have : Nonempty (OpenNormalSubgroup G) := ⟨M⟩
  let S (N : OpenNormalSubgroup G) : Set G :=
    {z | z ∉ (M : Subgroup G) ∧
      ∀ g : G, (g * z) * (z * g)⁻¹ ∈ (N : Subgroup G)}
  have hclosed (N : OpenNormalSubgroup G) : IsClosed (S N) := by
    change IsClosed ((M : Set G)ᶜ ∩ {z | ∀ g : G, (g * z) * (z * g)⁻¹ ∈ (N : Subgroup G)})
    apply IsClosed.inter M.isOpen.isClosed_compl
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro g
    exact N.isClosed.preimage
      ((continuous_const.mul continuous_id).mul ((continuous_id.mul continuous_const).inv))
  have hdir : Directed (· ⊇ ·) S := by
    intro N P
    refine ⟨N ⊓ P, ?_, ?_⟩
    · intro z hz
      exact ⟨hz.1, fun g => (hz.2 g).1⟩
    · intro z hz
      exact ⟨hz.1, fun g => (hz.2 g).2⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    S hdir hlift (fun N => (hclosed N).isCompact) hclosed
  have hzN (N : OpenNormalSubgroup G) : z ∈ S N := Set.mem_iInter.mp hz N
  refine ⟨z, ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro g
    exact mul_inv_eq_one.mp (eq_one_of_mem_all_openNormalSubgroups
      (fun N => (hzN N).2 g))
  · intro h
    exact (hzN M).1 (h.symm ▸ (M : Subgroup G).one_mem)

end ProCGroups.ProfiniteGrp
