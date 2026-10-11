/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Algebra.Group.Hom.Basic

/-!
# Ordinary faithfulness detected on a residual abelianization

The canonical projection from a group to its residual quotient induces a
map on topological abelianizations. Equality under ordinary conjugation
therefore implies equality under the actual residual conjugation action.
-/

namespace ProCGroups.ProC

open ProCGroups.Abelian

universe u

/-- Faithfulness on an abelianized residual quotient implies ordinary
abelianization-faithfulness of the same relative quotient. -/
theorem quotientConjugationTopologicalAbelianizationMap_injective_of_residual
    {C : FiniteGroupClass.{u}} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hfaith : Function.Injective (residualAbelianizationQuotientConjugation hC N hN)) :
    Function.Injective (quotientConjugationTopologicalAbelianizationMap N) := by
  apply (injective_iff_map_eq_one (quotientConjugationTopologicalAbelianizationMap N)).mpr
  intro a ha
  apply (injective_iff_map_eq_one (residualAbelianizationQuotientConjugation hC N hN)).mp
    hfaith a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
  apply MulEquiv.ext
  intro b
  obtain ⟨q, rfl⟩ := TopologicalAbelianization.surjective_mk
    (N ⧸ proCResidualCore C N) b
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C N) q
  let π : N →ₜ* (N ⧸ proCResidualCore C N) :=
    { toMonoidHom := QuotientGroup.mk' (proCResidualCore C N)
      continuous_toFun := QuotientGroup.continuous_mk }
  have hx := DFunLike.congr_fun ha (TopologicalAbelianization.mk N x)
  have hmap := congrArg (TopologicalAbelianization.map π) hx
  change TopologicalAbelianization.congr
    (residualQuotientConjugationContinuousMulEquiv hC N hN g)
    (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
      (QuotientGroup.mk' (proCResidualCore C N) x)) =
        TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
          (QuotientGroup.mk' (proCResidualCore C N) x)
  rw [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk]
  simp only [quotientConjugationTopologicalAbelianizationMap_mk_apply_mk,
    TopologicalAbelianization.map_apply_mk, MulAut.one_apply] at hmap
  change TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
    (QuotientGroup.mk' (proCResidualCore C N) (MulAut.conjNormal g x)) =
      TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
        (QuotientGroup.mk' (proCResidualCore C N) x) at hmap
  exact hmap

end ProCGroups.ProC
