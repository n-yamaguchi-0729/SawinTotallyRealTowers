import ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.ProC.Quotients.LeftQuotientMaps

set_option autoImplicit false

/-!
# Open-normal neighborhoods of closed subgroups

Given an open neighborhood of a closed subgroup, this file finds an open normal subgroup whose
intersection with the closed subgroup lies in that neighborhood, including a version whose finite
quotient belongs to a prescribed class.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
Given an open subgroup of a closed subgroup of a profinite group, one can shrink it to the
intersection with an ambient open normal subgroup.
-/
theorem exists_openNormalSubgroup_inter_closedSubgroup_le
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (H : ClosedSubgroup G) (U : OpenSubgroup H) :
    ∃ V : OpenNormalSubgroup G,
      (OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V : Subgroup H) ≤
        (U : Subgroup H) := by
  have hU_nhds : (((U : Subgroup H) : Set H)) ∈ 𝓝 (1 : H) := by
    exact U.isOpen'.mem_nhds U.one_mem'
  rcases (mem_nhds_subtype (H : Set G) (1 : H) (((U : Subgroup H) : Set H))).1 hU_nhds with
    ⟨W, hW_nhds, hWU⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W', hW'W, hW'open, h1W'⟩
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW'open h1W' with ⟨V, hVW'⟩
  refine ⟨V, ?_⟩
  intro x hx
  exact hWU <| by
    change x.1 ∈ W
    exact hW'W (hVW' hx)

omit [IsTopologicalGroup G] in
/--
Class-restricted version of \(exists_openNormalSubgroup_inter_closedSubgroup_le\) for a closed
subgroup of a pro-\(C\) group.
-/
theorem exists_openNormalSubgroupInClass_inter_closedSubgroup_le
    {C : FiniteGroupClass.{u}} (hG : HasOpenNormalBasisInClass C G)
    (H : ClosedSubgroup G) (U : OpenSubgroup H) :
    ∃ V : OpenNormalSubgroupInClass C G,
      (OpenNormalSubgroup.comap ((H : Subgroup G).subtype) continuous_subtype_val V.1 :
          Subgroup H) ≤
        (U : Subgroup H) := by
  have hU_nhds : (((U : Subgroup H) : Set H)) ∈ 𝓝 (1 : H) := by
    exact U.isOpen'.mem_nhds U.one_mem'
  rcases (mem_nhds_subtype (H : Set G) (1 : H) (((U : Subgroup H) : Set H))).1
      hU_nhds with
    ⟨W, hW_nhds, hWU⟩
  rcases mem_nhds_iff.mp hW_nhds with ⟨W', hW'W, hW'open, h1W'⟩
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW'open h1W' with
    ⟨V, hVW'⟩
  refine ⟨V, ?_⟩
  intro x hx
  exact hWU <| by
    change x.1 ∈ W
    exact hW'W (hVW' hx)

end ProCGroups.ProC
