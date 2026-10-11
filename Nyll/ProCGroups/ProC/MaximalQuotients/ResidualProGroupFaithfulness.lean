/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Topologies.QuotientMaps
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Ordinary faithfulness for pro-C subgroups

The identity map of a pro-C group kills its residual core, so that core is
trivial. The resulting actual quotient retraction carries residual
conjugation back to ordinary conjugation on topological abelianizations.
-/

namespace ProCGroups.ProC

open ProCGroups.Abelian

universe u

variable {C : FiniteGroupClass.{u}} {G : Type u}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G]

/-- A compact Hausdorff pro-C group has trivial residual core. -/
theorem proCResidualCore_eq_bot_of_hasOpenNormalBasisInClass
    (hC : FiniteGroupClass.Hereditary C)
    (hG : HasOpenNormalBasisInClass C G) : proCResidualCore C G = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  apply Subgroup.mem_bot.mpr
  exact (proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
    hC (ContinuousMonoidHom.id G) hG) hx

variable [TotallyDisconnectedSpace G]

/-- For a pro-C normal subgroup, ordinary quotient-conjugation faithfulness
implies faithfulness on its actual abelianized residual quotient. -/
theorem residualAbelianizationQuotientConjugation_injective_of_ordinary_of_proC
    (hC : FiniteGroupClass.FullFormation C)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))
    (hpro : HasOpenNormalBasisInClass C N)
    (hfaith : Function.Injective (quotientConjugationTopologicalAbelianizationMap N)) :
    Function.Injective (residualAbelianizationQuotientConjugation hC N hN) := by
  have : CompactSpace N := hN.isClosedEmbedding_subtypeVal.compactSpace
  have hR : proCResidualCore C N ≤ (ContinuousMonoidHom.id N).toMonoidHom.ker := by
    rw [proCResidualCore_eq_bot_of_hasOpenNormalBasisInClass hC.hereditary hpro]
    exact bot_le
  let r : N ⧸ proCResidualCore C N →ₜ* N :=
    QuotientGroup.liftₜ (proCResidualCore C N) (ContinuousMonoidHom.id N) hR
  have hr (x : N) : r (QuotientGroup.mk' (proCResidualCore C N) x) = x :=
    QuotientGroup.liftₜ_apply_mk (proCResidualCore C N) (ContinuousMonoidHom.id N) hR x
  apply (injective_iff_map_eq_one
    (residualAbelianizationQuotientConjugation hC N hN)).mpr
  intro a ha
  apply (injective_iff_map_eq_one
    (quotientConjugationTopologicalAbelianizationMap N)).mp hfaith a
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N a
  apply MulEquiv.ext
  intro b
  obtain ⟨x, rfl⟩ := TopologicalAbelianization.surjective_mk N b
  have hx := DFunLike.congr_fun ha
    (TopologicalAbelianization.mk (N ⧸ proCResidualCore C N)
      (QuotientGroup.mk' (proCResidualCore C N) x))
  have hmap := congrArg (TopologicalAbelianization.map r) hx
  change TopologicalAbelianization.mk N
      (r (QuotientGroup.mk' (proCResidualCore C N) (MulAut.conjNormal g x))) =
    TopologicalAbelianization.mk N
      (r (QuotientGroup.mk' (proCResidualCore C N) x)) at hmap
  rw [hr, hr] at hmap
  change TopologicalAbelianization.mk N (MulAut.conjNormal g x) =
    TopologicalAbelianization.mk N x
  exact hmap

end ProCGroups.ProC
