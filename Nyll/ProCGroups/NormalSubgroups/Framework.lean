/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Basic

/-!
# Closed normal closures and perfect subgroups

This module defines noncommutative groups, the universal property of a closed normal closure, and
perfect subgroups.
-/

noncomputable section

namespace ProCGroups

universe u

/-- A group is noncommutative when its abstract commutator subgroup is nontrivial. -/
def IsNoncommutativeGroup (G : Type u) [Group G] : Prop :=
  commutator G ≠ ⊥

namespace NormalSubgroups

/-- The closed normal closure of a subset as a universal closed normal subgroup. -/
def IsClosedNormalClosure {G : Type u} [Group G] [TopologicalSpace G]
    (S : Set G) (N : Subgroup G) : Prop :=
  N.Normal ∧ IsClosed (N : Set G) ∧ S ⊆ N ∧
    ∀ M : Subgroup G, M.Normal → IsClosed (M : Set G) → S ⊆ M → N ≤ M

/-- A subgroup is perfect when it is equal to its abstract commutator subgroup. -/
def IsPerfectSubgroup {G : Type u} [Group G] (K : Subgroup G) : Prop :=
  ⁅K, K⁆ = K

end NormalSubgroups
end ProCGroups
