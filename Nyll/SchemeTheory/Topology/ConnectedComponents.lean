/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Clopen
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Topology.Spectral.Prespectral

/-!
# Connected components of compact prespectral spaces

Compact open neighbourhoods and quasi-separatedness replace Hausdorff separation in the
description of connected components as intersections of clopen neighbourhoods.
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace SchemeTheory

variable {X : Type u} [TopologicalSpace X] [CompactSpace X]
  [PrespectralSpace X] [QuasiSeparatedSpace X]

/-- In a quasi-compact space with a basis of compact opens whose finite intersections are
compact, each connected component is the intersection of its clopen neighbourhoods. -/
@[stacks 005F]
theorem connectedComponent_eq_iInter_isClopen_of_prespectral (x : X) :
    connectedComponent x = ⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, s := by
  classical
  apply Subset.antisymm connectedComponent_subset_iInter_isClopen
  refine IsPreconnected.subset_connectedComponent ?_ (mem_iInter.2 fun s => s.2.2)
  have hS : IsClosed (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X)) :=
    isClosed_iInter fun s => s.2.1.1
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed hS]
  intro a b ha hb hab habDisjoint
  obtain ⟨U, hUcompact, hUopen, haU, hUb⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between ha.isCompact hb.isOpen_compl
      habDisjoint.subset_compl_right
  obtain ⟨V, hVcompact, hVopen, hbV, hVa⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hb.isCompact ha.isOpen_compl
      habDisjoint.symm.subset_compl_right
  -- Remove both the overlap and the part outside the compact open cover by one finite
  -- intersection of clopen neighbourhoods of x.
  let D : Set X := (U ∩ V) ∪ (U ∪ V)ᶜ
  have hDcompact : IsCompact D :=
    (hUcompact.inter_of_isOpen hVcompact hUopen hVopen).union
      (hUopen.union hVopen).isClosed_compl.isCompact
  have hDS : Disjoint D (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X)) := by
    apply Set.disjoint_left.mpr
    intro y hyD hyS
    rcases hyD with hyUV | hyOutside
    · rcases hab hyS with hya | hyb
      · exact hVa hyUV.2 hya
      · exact hUb hyUV.1 hyb
    · apply hyOutside
      rcases hab hyS with hya | hyb
      · exact Or.inl (haU hya)
      · exact Or.inr (hbV hyb)
  obtain ⟨indices, hindices⟩ := hDcompact.elim_finite_subfamily_closed
    (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => (s : Set X))
    (fun s => s.2.1.1) hDS
  let Z : Set X := ⋂ s ∈ indices, (s : Set X)
  have hZclopen : IsClopen Z := isClopen_biInter_finset fun s _ => s.2.1
  have hxZ : x ∈ Z := mem_iInter₂.2 fun s _ => s.2.2
  have hDZ : Disjoint D Z := hindices
  have hZcover : Z ⊆ U ∪ V := by
    intro y hyZ
    by_contra hyOutside
    exact Set.disjoint_left.mp hDZ (Or.inr hyOutside) hyZ
  have hZUV : Z ∩ U ∩ V = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact Set.disjoint_left.mp hDZ (Or.inl ⟨hy.1.2, hy.2⟩) hy.1.1
  have hZVU : Z ∩ V ∩ U = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    exact Set.disjoint_left.mp hDZ (Or.inl ⟨hy.2, hy.1.2⟩) hy.1.1
  have hZU : IsClopen (Z ∩ U) :=
    isClopen_inter_of_disjoint_cover_clopen' hZclopen hZcover hUopen hVopen hZUV
  have hZV : IsClopen (Z ∩ V) :=
    isClopen_inter_of_disjoint_cover_clopen' hZclopen
      (fun y hy => (hZcover hy).symm) hVopen hUopen hZVU
  by_cases hxU : x ∈ U
  · left
    have hSU : (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X)) ⊆ U :=
      (iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => (s : Set X))
        ⟨Z ∩ U, hZU, ⟨hxZ, hxU⟩⟩).trans inter_subset_right
    intro y hyS
    rcases hab hyS with hya | hyb
    · exact hya
    · exact (hUb (hSU hyS) hyb).elim
  · right
    have hxV : x ∈ V := (hZcover hxZ).resolve_left hxU
    have hSV : (⋂ s : { s : Set X // IsClopen s ∧ x ∈ s }, (s : Set X)) ⊆ V :=
      (iInter_subset (fun s : { s : Set X // IsClopen s ∧ x ∈ s } => (s : Set X))
        ⟨Z ∩ V, hZV, ⟨hxZ, hxV⟩⟩).trans inter_subset_right
    intro y hyS
    rcases hab hyS with hya | hyb
    · exact (hVa (hSV hyS) hya).elim
    · exact hyb

end SchemeTheory
