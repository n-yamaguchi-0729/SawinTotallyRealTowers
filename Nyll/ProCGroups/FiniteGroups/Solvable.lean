/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses

/-!
# Closure properties of finite solvable groups

This module packages the standard subgroup, finite-product, extension, formation, and hereditary
closure properties of `FiniteGroupClass.solvable`.
-/

namespace ProCGroups

universe u

namespace FiniteGroupClass

/-- A finite product of solvable groups is solvable. -/
private theorem isSolvable_pi_of_fintype
    {ι : Type u} [Finite ι]
    {G : ι → Type u} [∀ i, Group (G i)]
    (hG : ∀ i, Group.IsSolvable (G i)) :
    Group.IsSolvable (∀ i, G i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose n hn using fun i => (hG i).solvable
  let N : ℕ := ∑ i, n i
  refine ⟨⟨N, le_antisymm ?_ bot_le⟩⟩
  intro x hx
  apply Subgroup.mem_bot.mpr
  funext i
  have hxi : x i ∈ derivedSeries (G i) N := by
    exact (map_derivedSeries_le_derivedSeries (Pi.evalMonoidHom G i) N) ⟨x, hx, rfl⟩
  have hni : n i ≤ N := by
    dsimp [N]
    exact Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hxi' : x i ∈ derivedSeries (G i) (n i) :=
    (derivedSeries_antitone (G i) hni) hxi
  rw [hn i] at hxi'
  exact Subgroup.mem_bot.mp hxi'

/-- Finite solvable groups are closed under subgroups. -/
theorem solvable_subgroupClosed : SubgroupClosed solvable := by
  intro G _ H hG
  rcases hG with ⟨hfinite, hsolvable⟩
  refine ⟨Finite.of_injective ((↑) : H → G) Subtype.coe_injective, ?_⟩
  exact Group.isSolvable_of_isSolvable_injective (f := H.subtype) H.subtype_injective

/-- Finite solvable groups are closed under finite direct products. -/
theorem solvable_finiteProductClosed : FiniteProductClosed solvable := by
  intro ι _ G _ hG
  refine ⟨?_, isSolvable_pi_of_fintype fun i => (hG i).2⟩
  let : ∀ i, Finite (G i) := fun i => (hG i).1
  exact Pi.finite (α := ι) (β := G)

/-- Finite solvable groups form a variety of finite groups. -/
theorem solvable_variety : Variety solvable :=
  ⟨solvable_subgroupClosed, solvable_quotientClosed, solvable_finiteProductClosed⟩

/-- Finite solvable groups form a formation. -/
theorem solvable_formation : Formation solvable :=
  variety_formation solvable_variety solvable_isomClosed

/-- Finite solvable groups are closed under extensions. -/
theorem solvable_extensionClosed : ExtensionClosed solvable := by
  intro E _ N _ hN hQ
  rcases hN with ⟨hNfinite, hNsolvable⟩
  rcases hQ with ⟨hQfinite, hQsolvable⟩
  exact ⟨finite_of_finite_normalSubgroup_and_quotient (N := N),
    (Group.isSolvable_iff_subgroup_quotient N).2 ⟨hNsolvable, hQsolvable⟩⟩

/-- Finite solvable groups are closed under normal subgroups. -/
theorem solvable_normalSubgroupClosed : NormalSubgroupClosed solvable := by
  intro G _ N _ hG
  exact solvable_subgroupClosed N hG

/-- Finite solvable groups form a Melnikov formation. -/
theorem solvable_melnikovFormation : MelnikovFormation solvable where
  formation := solvable_formation
  normalSubgroupClosed := solvable_normalSubgroupClosed
  extensionClosed := solvable_extensionClosed

/-- Finite solvable groups form a full formation. -/
theorem solvable_fullFormation : FullFormation solvable where
  melnikovFormation := solvable_melnikovFormation
  subgroupClosed := solvable_subgroupClosed

/-- Finite solvable groups form a hereditary finite-group class. -/
theorem solvable_hereditary : Hereditary solvable :=
  solvable_fullFormation.hereditary

end FiniteGroupClass

end ProCGroups
