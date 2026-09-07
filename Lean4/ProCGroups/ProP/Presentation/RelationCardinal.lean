import ProCGroups.ProP.Presentation.GeneratorRank

set_option autoImplicit false
/-!
# Minimal relation cardinal

The relation rank is defined only after an actual finite minimal presentation
witness has been constructed.  It is the least displayed relation count among
such presentations; no existence or comparison theorem is hidden in the
definition.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups

noncomputable section

universe u

/-- A profinite group admits an actual finite minimal pro-`p` presentation. -/
def HasFiniteMinimalPresentation
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ∃ sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p),
    ∃ d r, ∃ P : FiniteProPPresentation p d r sourceData G, P.IsMinimal

/-- Relation counts realized by finite minimal presentations. -/
def relationCounts
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Set ℕ :=
  {r | ∃ sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p),
    ∃ d, ∃ P : FiniteProPPresentation p d r sourceData G, P.IsMinimal}

/-- A finite minimal presentation witness makes the set of relation counts
nonempty. -/
theorem relationCounts_nonempty
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasFiniteMinimalPresentation p G) :
    (relationCounts p G).Nonempty := by
  rcases hG with ⟨sourceData, d, r, P, hP⟩
  exact ⟨r, sourceData, d, P, hP⟩

/-- The least relation count among actual finite minimal presentations. -/
noncomputable def minimalRelationRank
    (p : ℕ) [Fact p.Prime]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (_hG : HasFiniteMinimalPresentation p G) : ℕ :=
  sInf (relationCounts p G)

/-- The least relation count is itself realized by a finite minimal
presentation. -/
theorem minimalRelationRank_mem_relationCounts
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasFiniteMinimalPresentation p G) :
    minimalRelationRank p G hG ∈ relationCounts p G := by
  exact Nat.sInf_mem (relationCounts_nonempty hG)

/-- Every concrete minimal presentation bounds the least relation rank. -/
theorem FiniteProPPresentation.minimalRelationRank_le
    {p d r : ℕ} [Fact p.Prime]
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal)
    (hG : HasFiniteMinimalPresentation p G) :
    minimalRelationRank p G hG ≤ r := by
  apply Nat.sInf_le
  exact ⟨sourceData, d, P, hP⟩

/-- Some concrete finite minimal presentation realizes the least relation
rank. -/
theorem exists_presentation_relationCard_eq_minimal
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasFiniteMinimalPresentation p G) :
    ∃ sourceData :
        FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
          (FiniteGroupClass.pGroup p),
      ∃ d, ∃ P : FiniteProPPresentation p d (minimalRelationRank p G hG)
          sourceData G,
        P.IsMinimal :=
  minimalRelationRank_mem_relationCounts hG

end


end ClassFieldTower.ProP
