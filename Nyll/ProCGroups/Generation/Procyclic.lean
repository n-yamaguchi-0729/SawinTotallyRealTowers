/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Generation.QuotientCriteria
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Topology.Compactness.Compact

/-!
# A topological generator from cyclic finite quotients

For each open normal quotient, the lifts of its generators form a closed subset of the original
compact group. A generator of a common finite quotient solves any finite family of these
conditions. Compactness supplies one element satisfying all of them, and the finite-quotient
criterion proves that this element topologically generates the original group.
-/

open Set
open scoped Topology

namespace ProCGroups.Generation

open ProCGroups.ProC

universe u

/-- A profinite group all of whose open normal quotients are cyclic has an actual topological
generator. The compatible generator is obtained by compactness, not given as extra data. -/
theorem exists_topologicallyGenerates_singleton_of_cyclic_quotients
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hcyclic : ∀ U : OpenNormalSubgroup G, IsCyclic (G ⧸ (U : Subgroup G))) :
    ∃ g : G, TopologicallyGenerates ({g} : Set G) := by
  classical
  let generators : OpenNormalSubgroup G → Set G := fun U =>
    {g | Subgroup.zpowers (OpenNormalSubgroup.quotientProj U g) = ⊤}
  have closedGenerators : ∀ U, IsClosed (generators U) := by
    intro U
    exact (isClosed_discrete
      {a : G ⧸ (U : Subgroup G) | Subgroup.zpowers a = ⊤}).preimage
        (OpenNormalSubgroup.quotientProj U).continuous
  have refinement : ∀ s : Finset (OpenNormalSubgroup G),
      ∃ V : OpenNormalSubgroup G, ∀ U ∈ s, (V : Subgroup G) ≤ (U : Subgroup G) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨⊤, fun U hU => False.elim (Finset.notMem_empty U hU)⟩
    | @insert U s _ ih =>
      obtain ⟨V, hV⟩ := ih
      refine ⟨U ⊓ V, fun W hW => ?_⟩
      rcases Finset.mem_insert.mp hW with rfl | hW
      · exact fun g hg => hg.1
      · exact fun g hg => hV W hW hg.2
  have finiteIntersection : ∀ s : Finset (OpenNormalSubgroup G),
      (⋂ U ∈ s, generators U).Nonempty := by
    intro s
    obtain ⟨V, hV⟩ := refinement s
    have cyclicV : IsCyclic (G ⧸ (V : Subgroup G)) := hcyclic V
    obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := G ⧸ (V : Subgroup G))
    obtain ⟨g, rfl⟩ := OpenNormalSubgroup.quotientProj_surjective V a
    refine ⟨g, Set.mem_iInter.mpr fun U => Set.mem_iInter.mpr fun hU => ?_⟩
    apply top_unique
    intro x _
    let transition := OpenNormalSubgroup.transition (hV U hU)
    obtain ⟨y, rfl⟩ := OpenNormalSubgroup.transition_surjective (hV U hU) x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha y)
    apply Subgroup.mem_zpowers_iff.mpr
    refine ⟨n, ?_⟩
    have h := congrArg transition hn
    rw [map_zpow] at h
    exact h
  obtain ⟨g, hg⟩ := CompactSpace.iInter_nonempty closedGenerators finiteIntersection
  refine ⟨g, topologicallyGenerates_iff_forall_quotientProj_image.mpr fun U => ?_⟩
  have hU : Subgroup.zpowers (OpenNormalSubgroup.quotientProj U g) = ⊤ :=
    Set.mem_iInter.mp hg U
  rw [Set.image_singleton, TopologicallyGenerates, ← Subgroup.zpowers_eq_closure, hU]
  exact top_unique (Subgroup.le_topologicalClosure ⊤)

end ProCGroups.Generation
