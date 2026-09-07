import Mathlib.Topology.Algebra.ClopenNhdofOne

set_option autoImplicit false

/-!
# Open-normal neighborhood bases at the identity

Every identity neighborhood in a profinite group contains an open normal subgroup. This file
packages that refinement result for later basis, separation, and inverse-limit arguments.
-/

namespace ProCGroups.ProC

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
In a compact totally disconnected topological group, any open neighborhood of \(1\) contains an
open normal subgroup.
-/
theorem exists_openNormalSubgroup_sub_open_nhds_of_one [CompactSpace G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U : OpenNormalSubgroup G, ((U : Subgroup G) : Set G) ⊆ W := by
  obtain ⟨U, hU⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1W
  exact ⟨U, fun _ hx ↦ hU hx⟩

end

end ProCGroups.ProC
