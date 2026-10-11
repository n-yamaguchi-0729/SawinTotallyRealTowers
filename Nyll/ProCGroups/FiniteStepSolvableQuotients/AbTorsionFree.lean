/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Abelianization

/-!
# Ab-torsion-freeness

The topological abelianization of every open subgroup is torsion-free.
These are general topological-group definitions and consequences.
-/

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian

universe u

/-- Every open subgroup has torsion-free topological abelianization. -/
def IsAbTorsionFree
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : Prop :=
  ∀ H : OpenSubgroup G, IsMulTorsionFree (TopologicalAbelianization ↥(H : Subgroup G))

/-- Ab-torsion-freeness implies torsion-freeness of the ambient
topological abelianization. -/
theorem isMulTorsionFree_topologicalAbelianization_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hG : IsAbTorsionFree G) :
    IsMulTorsionFree (TopologicalAbelianization G) := by
  let e := topologicalAbelianizationTopMulEquiv (G := G)
  let :
      IsMulTorsionFree (TopologicalAbelianization ↥((⊤ : OpenSubgroup G) : Subgroup G)) := hG ⊤
  exact e.isMulTorsionFree

/-- For a commutative `T₁` topological group, ab-torsion-freeness
implies torsion-freeness of the group itself. -/
theorem isMulTorsionFree_of_isAbTorsionFree_commGroup
    {G : Type u} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G] [T1Space G]
    (hG : IsAbTorsionFree G) :
    IsMulTorsionFree G := by
  let : IsMulTorsionFree (TopologicalAbelianization G) :=
    isMulTorsionFree_topologicalAbelianization_of_isAbTorsionFree (G := G) hG
  exact (TopologicalAbelianization.continuousMulEquivOfCommGroup G).isMulTorsionFree

end ProCGroups.FiniteStepSolvableQuotients
