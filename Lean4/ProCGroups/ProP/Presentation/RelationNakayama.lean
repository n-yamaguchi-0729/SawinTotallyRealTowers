import ProCGroups.ProP.Presentation.RelationCardinal
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.Presentations

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Omitting a displayed relator that already belongs to the closed normal
closure of the other relators produces a presentation with one fewer
displayed relation. -/
theorem exists_presentation_of_relator_mem_others
    {d n : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (P : FiniteProPPresentation p d (n + 1) sourceData G)
    (i : Fin (n + 1))
    (hi : P.relator i ∈ closedNormalClosure
      (Set.range (fun j : Fin n ↦ P.relator (i.succAbove j)))) :
    ∃ P' : FiniteProPPresentation p d n sourceData G,
      P'.IsMinimal ↔ P.IsMinimal := by
  let rel' : Fin n → sourceData.carrier :=
    fun j ↦ P.relator (i.succAbove j)
  have hsub : Set.range rel' ⊆ Set.range P.relator := by
    rintro _ ⟨j, rfl⟩
    exact ⟨i.succAbove j, rfl⟩
  have hall : Set.range P.relator ⊆ closedNormalClosure (Set.range rel') := by
    rintro _ ⟨j, rfl⟩
    by_cases hji : j = i
    · simpa [hji, rel'] using hi
    · let k : Fin n := (finSuccAboveEquiv i).symm ⟨j, hji⟩
      have hk : i.succAbove k = j := by
        change ((finSuccAboveEquiv i) k).1 = j
        simp [k]
      exact subset_closedNormalClosure (Set.range rel') ⟨k, by simp [rel', hk]⟩
  have hclosure : closedNormalClosure (Set.range rel') =
      closedNormalClosure (Set.range P.relator) := by
    apply le_antisymm
    · exact closedNormalClosure_le_closed_normal
        (closedNormalClosure_isClosed (Set.range P.relator))
        (hsub.trans (subset_closedNormalClosure (Set.range P.relator)))
    · exact closedNormalClosure_le_closed_normal
        (closedNormalClosure_isClosed (Set.range rel')) hall
  let hPresentation : IsFreePresentationOf
      (X := ULift.{u} (Fin d))
      (F := sourceData.carrier)
      (G := G)
      (FiniteGroupClass.pGroup p)
      (CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard
        sourceData P.basisCard)
      (Set.range rel') :=
    ⟨P.isPresentation.1, P.isPresentation.2.1,
      ⟨P.quotient, P.quotient_surjective, by
        rw [P.kernel_eq_closedNormalClosure, hclosure]⟩⟩
  let P' : FiniteProPPresentation p d n sourceData G :=
    { basisCard := P.basisCard
      relator := rel'
      isPresentation := hPresentation }
  refine ⟨P', ?_⟩
  constructor <;> intro h
  · rw [FiniteProPPresentation.IsMinimal,
      P.kernel_eq_closedNormalClosure, ← hclosure,
      ← P'.kernel_eq_closedNormalClosure]
    exact h
  · rw [FiniteProPPresentation.IsMinimal,
      P'.kernel_eq_closedNormalClosure, hclosure,
      ← P.kernel_eq_closedNormalClosure]
    exact h

/-- A presentation realizing the minimal relation number is irredundant as a
closed normal generating family. -/
theorem relator_not_mem_closedNormalClosure_others_of_relationCard_minimal
    {d n : ℕ}
    {sourceData :
      FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (FiniteGroupClass.pGroup p)}
    (hG : HasFiniteMinimalPresentation p G)
    (P : FiniteProPPresentation p d (n + 1) sourceData G)
    (hP : P.IsMinimal)
    (hcard : minimalRelationRank p G hG = n + 1)
    (i : Fin (n + 1)) :
    P.relator i ∉ closedNormalClosure
      (Set.range (fun j : Fin n ↦ P.relator (i.succAbove j))) := by
  intro hi
  obtain ⟨P', hP'⟩ :=
    exists_presentation_of_relator_mem_others P i hi
  have hle := P'.minimalRelationRank_le (hP'.2 hP) hG
  rw [hcard] at hle
  exact Nat.not_succ_le_self n hle


end

end ClassFieldTower.ProP
