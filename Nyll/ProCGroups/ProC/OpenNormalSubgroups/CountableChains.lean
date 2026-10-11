/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Profinite.Basic

/-!
# Countable descending open-normal chains

This file defines countable open-normal bases at the identity and characterizes them by descending
chains with trivial intersection. It also supplies the refinement property needed to use such
chains as neighborhood bases.
-/

namespace ProCGroups.ProC

universe u v

section

variable {G : Type u} [Group G] [TopologicalSpace G]

/--
Preparatory countable-chain layer for later use: \(1\) has a countable fundamental system of
open normal subgroups. This isolates the part of the corollary that does not yet depend on the
not-yet-formalized cardinal invariant \(w_0(G)\) or on the generator-counting statements from
the later section on generators.
-/
def HasCountableOpenNormalBasisAtOne
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U : ℕ → OpenNormalSubgroup G,
    Antitone (fun n => (U n : Subgroup G)) ∧
    ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
      ∃ n : ℕ, (((U n : Subgroup G) : Set G)) ⊆ W

/--
Compactness lemma for descending families of closed subgroups: if the total intersection lies
inside an open subgroup, then one term already lies inside that open subgroup.
-/
theorem exists_term_le_openSubgroup_of_iInf_le [CompactSpace G]
    (H : ℕ → Subgroup G) (hmono : Antitone H)
    (hclosed : ∀ n, IsClosed (((H n : Subgroup G) : Set G)))
    (U : OpenSubgroup G) (hInf : iInf H ≤ (U : Subgroup G)) :
    ∃ n : ℕ, H n ≤ (U : Subgroup G) := by
  let K : Set G := (((U : Subgroup G) : Set G))ᶜ
  have hKclosed : IsClosed K := by
    simpa [K] using (openSubgroup_isOpen (G := G) U).isClosed_compl
  have hKcompact : IsCompact K := hKclosed.isCompact
  have havoid : K ∩ ⋂ n, (((H n : Subgroup G) : Set G)) = ∅ := by
    ext x
    constructor
    · intro hx
      have hxInf : x ∈ iInf H := by
        simpa using hx.2
      exact False.elim (hx.1 (hInf hxInf))
    · intro hx
      simp only [Set.mem_empty_iff_false] at hx
  have hdir : Directed (fun s t : Set G => s ⊇ t) (fun n => (((H n : Subgroup G) : Set G))) := by
    intro i j
    refine ⟨max i j, ?_, ?_⟩
    · exact hmono (Nat.le_max_left i j)
    · exact hmono (Nat.le_max_right i j)
  have havoid' : Disjoint K (⋂ n, (((H n : Subgroup G) : Set G))) := by
    rw [Set.disjoint_left]
    intro x hxK hxH
    have hx : x ∈ K ∩ ⋂ n, (((H n : Subgroup G) : Set G)) := ⟨hxK, hxH⟩
    rw [havoid] at hx
    exact hx
  rcases hKcompact.elim_directed_family_closed
      (fun n => (((H n : Subgroup G) : Set G))) hclosed
      havoid' hdir with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro x hx
  by_contra hxU
  have hxK : x ∈ K := by
    simpa [K] using hxU
  exact (Set.disjoint_left.mp hn) hxK hx

/--
Preparatory countable-chain / neighborhood-basis equivalence for profinite groups: for a
profinite group, giving a countable descending chain of open normal subgroups with trivial
intersection is equivalent to giving a countable neighborhood basis at \(1\) formed by a
descending chain of open normal subgroups. This is exactly the chain-theoretic content of the
corollary; the generator-cardinality half will be added later once the \(w_0(G)\) /
convergent-generator formulation is in place.
-/
theorem hasCountableOpenNormalBasisAtOne_iff_exists_descending_openNormalChain
    [IsTopologicalGroup G] [CompactSpace G] [T1Space G] [TotallyDisconnectedSpace G] :
    HasCountableOpenNormalBasisAtOne G ↔
      ∃ U : ℕ → OpenNormalSubgroup G,
        Antitone (fun n => (U n : Subgroup G)) ∧
        iInf (fun n => (U n : Subgroup G)) = (⊥ : Subgroup G) := by
  constructor
  · rintro ⟨U, hmono, hbasis⟩
    refine ⟨U, hmono, ?_⟩
    apply le_antisymm
    · intro x hx
      change x = 1
      by_contra hxne
      let W : Set G := ({x} : Set G)ᶜ
      have hW : IsOpen W := by
        simp only [isOpen_compl_iff, Set.finite_singleton, Set.Finite.isClosed, W]
      have h1W : (1 : G) ∈ W := by
        have hx1 : (1 : G) ≠ x := by
          intro h1x
          exact hxne h1x.symm
        simpa [W] using hx1
      rcases hbasis W hW h1W with ⟨n, hnW⟩
      have hxall : ∀ n : ℕ, x ∈ (((U n : Subgroup G) : Set G)) := by
        simpa using hx
      have hxW : x ∈ W := hnW (hxall n)
      have : x ∉ ({x} : Set G) := by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, not_true_eq_false, W] at hxW
      exact this (by simp only [Set.mem_singleton_iff])
    · exact bot_le
  · rintro ⟨U, hmono, hinf⟩
    refine ⟨U, hmono, ?_⟩
    intro W hW h1W
    rcases ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
        (G := G) hW h1W with ⟨N, hNW⟩
    have hInfLe : iInf (fun n => (U n : Subgroup G)) ≤ (N : Subgroup G) := by
      simp only [hinf, bot_le]
    rcases exists_term_le_openSubgroup_of_iInf_le (G := G)
        (fun n => (U n : Subgroup G)) hmono
        (fun n => openNormalSubgroup_isClosed (G := G) (U n))
        N.toOpenSubgroup hInfLe with ⟨n, hnN⟩
    exact ⟨n, fun x hx => hNW (hnN hx)⟩

end

end ProCGroups.ProC
