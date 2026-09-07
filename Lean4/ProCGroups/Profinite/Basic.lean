import ProCGroups.Profinite.OpenSubgroups

set_option autoImplicit false

/-!
# Separation in profinite groups

This module proves that an element of a profinite group lying in every open normal subgroup is
the identity.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups

universe u

section Permanence

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace ProfiniteGrp

/-- In a profinite group, an element lying in every open normal subgroup must be \(1\). -/
theorem eq_one_of_mem_all_openNormalSubgroups [CompactSpace G]
    [TotallyDisconnectedSpace G] {x : G}
    (hx : ∀ U : OpenNormalSubgroup G, x ∈ (U : Subgroup G)) : x = 1 := by
  by_contra hxne
  let W : Set G := ({x} : Set G)ᶜ
  have hW : IsOpen W := by
    simp only [isOpen_compl_iff, finite_singleton, Finite.isClosed, W]
  have h1W : (1 : G) ∈ W := by
    have hx1 : (1 : G) ≠ x := by
      intro h1x
      exact hxne h1x.symm
    simp only [mem_compl_iff, mem_singleton_iff, hx1, not_false_eq_true, W]
  rcases ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (G := G) hW h1W with ⟨U, hUW⟩
  have hxU : x ∈ (U : Subgroup G) := hx U
  have hxW : x ∈ W := hUW hxU
  simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, W] at hxW

end ProfiniteGrp

end Permanence

end ProCGroups
