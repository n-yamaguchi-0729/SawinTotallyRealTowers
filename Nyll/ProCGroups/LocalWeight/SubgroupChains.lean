/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.CountableChains

/-!
# Intersections of subgroup chains

This file packages linearly ordered families of subgroups, defines their carrier union and
intersection, and gives membership and trivial-intersection criteria used in transfinite
closed-normal series arguments.
-/

namespace ProCGroups.LocalWeight

universe u v


section Chains

variable {ι : Type v}
variable {G : Type u} [Group G]

/-- A family of subgroups forming a chain indexed for transfinite local-weight statements. -/
abbrev SubgroupChain (ι : Type v) (G : Type u) [Group G] := ι → Subgroup G

/-- The set-theoretic union of the members of a subgroup chain. -/
def subgroupChainCarrier (c : SubgroupChain ι G) : Set G :=
  { g | ∃ i, g ∈ c i }

/-- The infimum of all members of a subgroup chain. -/
def subgroupChainInf (c : SubgroupChain ι G) : Subgroup G :=
  sInf (Set.range c)

/--
Membership in the carrier of a subgroup chain is equivalent to the displayed coordinate
condition.
-/
@[simp] theorem mem_subgroupChainCarrier_iff {c : SubgroupChain ι G} {g : G} :
    g ∈ subgroupChainCarrier c ↔ ∃ i, g ∈ c i :=
  Iff.rfl

/-- The infimum of a subgroup chain is contained in each subgroup in the chain. -/
theorem subgroupChainInf_le (c : SubgroupChain ι G) (i : ι) :
    subgroupChainInf c ≤ c i := by
  exact sInf_le (Set.mem_range_self i)

/--
Membership in the infimum of a subgroup chain is equivalent to the displayed coordinate
condition.
-/
@[simp] theorem mem_subgroupChainInf_iff {c : SubgroupChain ι G} {g : G} :
    g ∈ subgroupChainInf c ↔ ∀ i, g ∈ c i := by
  simp only [subgroupChainInf, Subgroup.mem_sInf, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff]

/--
The subgroup-chain infimum is trivial exactly when every nontrivial element is excluded at some
stage.
-/
theorem subgroupChainInf_eq_bot_iff {c : SubgroupChain ι G} :
    subgroupChainInf c = ⊥ ↔ ∀ g : G, (∀ i, g ∈ c i) → g = 1 := by
  constructor
  · intro h g hg
    have hmem : g ∈ subgroupChainInf c := by
      exact (mem_subgroupChainInf_iff.mpr hg)
    have : g ∈ (⊥ : Subgroup G) := by
      simpa [h] using hmem
    simpa using this
  · intro h
    ext g
    constructor
    · intro hg
      have hgall : ∀ i, g ∈ c i :=
        mem_subgroupChainInf_iff.mp hg
      have : g = 1 := h g hgall
      simp only [this, one_mem]
    · intro hg
      have hg1 : g = 1 := by
        simpa using hg
      subst hg1
      exact (mem_subgroupChainInf_iff).2 (fun i => (c i).one_mem)

/--
The infimum of a subgroup chain is bottom exactly when every nontrivial element is excluded at
some stage.
-/
theorem subgroupChainInf_eq_bot_iff_forall_ne_one {c : SubgroupChain ι G} :
    subgroupChainInf c = ⊥ ↔ ∀ g : G, g ≠ 1 → ∃ i, g ∉ c i := by
  constructor
  · intro h g hg
    by_contra hneg
    have hgall : ∀ i, g ∈ c i := by
      intro i
      by_contra hgi
      exact hneg ⟨i, hgi⟩
    have hbot : ∀ x : G, (∀ i, x ∈ c i) → x = 1 :=
      (subgroupChainInf_eq_bot_iff (c := c)).mp h
    exact hg (hbot g hgall)
  · intro h
    rw [subgroupChainInf_eq_bot_iff (c := c)]
    intro g hgall
    by_contra hg1
    rcases h g hg1 with ⟨i, hgi⟩
    exact hgi (hgall i)

end Chains

end ProCGroups.LocalWeight
