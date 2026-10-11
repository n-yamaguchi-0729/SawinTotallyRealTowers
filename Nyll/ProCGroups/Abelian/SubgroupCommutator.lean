/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients

/-!
# Closed commutators of closed subgroups

For a closed subgroup, the image of its closed commutator under the
subgroup inclusion is the topological closure of its commutator in the
ambient group.
-/

open scoped commutatorElement
namespace ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients ProCGroups.Abelian
universe u

theorem map_closedCommutator_subtype
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (D : Subgroup G) (hD : IsClosed (D : Set G)) :
    (Subgroup.closedCommutator D).map D.subtype = ⁅D, D⁆.topologicalClosure := by
  let f : D →ₜ* G := ⟨D.subtype, continuous_subtype_val⟩
  have htop : (⊤ : Subgroup D).map f.toMonoidHom = D := by
    rw [Subgroup.map_top]
    exact D.range_subtype
  change (closedCommutator (⊤ : Subgroup D) ⊤).map f.toMonoidHom =
    closedCommutator D D
  apply map_closedCommutator_eq_of_map_eq (f := f) htop htop
  exact hD.isClosedMap_subtype_val _ (Subgroup.isClosed_closedCommutator D)

end ProCGroups.Abelian
