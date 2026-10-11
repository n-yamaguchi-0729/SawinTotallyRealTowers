/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Abelianization faithfulness

Every open subgroup acts faithfully on the topological abelianization of
each open normal subgroup. The relative pro-Σ version uses the same
quotient-conjugation action on the maximal pro-Σ quotient.
-/

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC ProCGroups.Abelian

universe u

/-- Every open subgroup acts faithfully on the topological abelianization
of each open normal subgroup. -/
def IsAbFaithful
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] : Prop :=
  ∀ H : OpenSubgroup G,
    ∀ N : OpenNormalSubgroup ↥(H : Subgroup G),
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap
          (G := ↥(H : Subgroup G)) (N := (N : Subgroup ↥(H : Subgroup G))))

/-- Definition in Section 1: every finite relative quotient acts faithfully
on the abelianized maximal pro-`Σ` quotient of its open normal subgroup. -/
def IsSigmaAbFaithful (sigma : Set ℕ) (G : Type u)
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : Prop :=
  ∀ H : OpenSubgroup G,
    letI : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    ∀ N : OpenNormalSubgroup (H : Subgroup G),
      Function.Injective
        (residualAbelianizationQuotientConjugation
          (FiniteGroupClass.sigmaGroup_fullFormation sigma)
          (N : Subgroup (H : Subgroup G)) N.isClosed)

end ProCGroups.FiniteStepSolvableQuotients
