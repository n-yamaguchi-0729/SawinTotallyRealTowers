/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation

/-!
# Detecting conjugacy in finite quotients

In a profinite group, a conjugacy class is compact and hence closed.  Thus two
elements are conjugate exactly when their images are conjugate in every
open-normal quotient.
-/

namespace ProCGroups.Boundary

universe u

/-- Two elements of a profinite group are conjugate if and only if their
images are conjugate in every open-normal finite quotient. -/
theorem isConj_iff_forall_openNormal_quotient_isConj
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {x y : G} :
    IsConj x y ↔
      ∀ U : OpenNormalSubgroup G,
        IsConj
          (QuotientGroup.mk' (U : Subgroup G) x)
          (QuotientGroup.mk' (U : Subgroup G) y) := by
  constructor
  · intro hxy U
    exact (QuotientGroup.mk' (U : Subgroup G)).map_isConj hxy
  · intro hxy
    let S : Set G := (fun g : G ↦ g * x * g⁻¹) '' Set.univ
    have hSclosed : IsClosed S := by
      have hcontinuous : Continuous (fun g : G ↦ g * x * g⁻¹) :=
        (continuous_id.mul continuous_const).mul continuous_inv
      exact (isCompact_univ.image hcontinuous).isClosed
    have hyS : y ∈ S :=
      (ProCGroups.mem_closed_iff_forall_openNormal_quotient hSclosed).mpr (by
        intro U
        obtain ⟨qg, hqg⟩ := isConj_iff.mp (hxy U)
        obtain ⟨g, rfl⟩ :=
          (QuotientGroup.mk'_surjective (U : Subgroup G)) qg
        refine ⟨g * x * g⁻¹, ⟨g, Set.mem_univ g, rfl⟩, ?_⟩
        simpa only [map_mul, map_inv] using hqg)
    obtain ⟨g, _hg, hg⟩ := hyS
    exact isConj_iff.mpr ⟨g, hg⟩

end ProCGroups.Boundary
