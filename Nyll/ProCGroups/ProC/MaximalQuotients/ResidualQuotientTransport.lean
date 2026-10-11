/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.Topologies.QuotientMaps
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homeomorph.Defs

/-!
# Transport of residual quotient conjugation

An ambient continuous group equivalence transports a closed subgroup's
intrinsic residual quotient. The induced equivalence on topological
abelianizations intertwines actual conjugation, so the corresponding
quotient actions are faithful simultaneously.
-/

namespace ProCGroups.ProC

open ProCGroups.Abelian

universe u

variable {C : FiniteGroupClass.{u}}
variable {G H : Type u} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]

private def subgroupMapContinuousMulEquiv (e : G ≃ₜ* H) (N : Subgroup G) :
    N ≃ₜ* N.map e.toMulEquiv.toMonoidHom where
  toMulEquiv := e.toMulEquiv.subgroupMap N
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact e.continuous_toFun.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact e.symm.continuous_toFun.comp continuous_subtype_val

private theorem subgroupMap_normal (e : G ≃ₜ* H) (N : Subgroup G) [h : N.Normal] :
    (N.map e.toMulEquiv.toMonoidHom).Normal :=
  h.map e.toMulEquiv.toMonoidHom e.surjective

private theorem subgroupMap_isClosed (e : G ≃ₜ* H) (N : Subgroup G)
    (hN : IsClosed (N : Set G)) :
    IsClosed ((N.map e.toMulEquiv.toMonoidHom : Subgroup H) : Set H) :=
  e.toHomeomorph.isClosedMap N hN

attribute [local instance] subgroupMap_normal

variable [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [T2Space G] [T2Space H] [TotallyDisconnectedSpace G]

/-- An ambient equivalence induces an equivalence of the actual residual
quotients of a closed subgroup and its image. -/
noncomputable def residualQuotientSubgroupTransport
    (hC : FiniteGroupClass.FullFormation C) (e : G ≃ₜ* H)
    (N : Subgroup G) (hN : IsClosed (N : Set G)) :
    N ⧸ proCResidualCore C N ≃ₜ*
      N.map e.toMulEquiv.toMonoidHom ⧸
        proCResidualCore C (N.map e.toMulEquiv.toMonoidHom) := by
  have : CompactSpace N := hN.isClosedEmbedding_subtypeVal.compactSpace
  let r : N ≃ₜ* N.map e.toMulEquiv.toMonoidHom :=
    subgroupMapContinuousMulEquiv e N
  have hmap : (proCResidualCore C N).map r.toMulEquiv.toMonoidHom =
      proCResidualCore C (N.map e.toMulEquiv.toMonoidHom) :=
    map_proCResidualCore_eq_of_surjective hC r.toMulEquiv.toMonoidHom
      r.continuous_toFun r.surjective
      (proCResidualCoreQuotient_hasOpenNormalBasisInClass hC.melnikovFormation.formation)
  exact QuotientGroup.congrₜ (proCResidualCore C N)
    (proCResidualCore C (N.map e.toMulEquiv.toMonoidHom)) r hmap

/-- Transport is evaluated by the original ambient equivalence. -/
theorem residualQuotientSubgroupTransport_apply_mk
    (hC : FiniteGroupClass.FullFormation C) (e : G ≃ₜ* H)
    (N : Subgroup G) (hN : IsClosed (N : Set G)) (x : N) :
    residualQuotientSubgroupTransport hC e N hN
        (QuotientGroup.mk' (proCResidualCore C N) x) =
      QuotientGroup.mk' (proCResidualCore C (N.map e.toMulEquiv.toMonoidHom))
        (e.toMulEquiv.subgroupMap N x) := by
  rfl

variable [CompactSpace H] [TotallyDisconnectedSpace H]

/-- The induced transport on abelianizations intertwines actual ambient
conjugation, with the conjugating element transported by the same equivalence. -/
theorem residualAbelianizationSubgroupTransport_conjugation
    (hC : FiniteGroupClass.FullFormation C) (e : G ≃ₜ* H)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (g : G)
    (a : TopologicalAbelianization (N ⧸ proCResidualCore C N)) :
    TopologicalAbelianization.congr (residualQuotientSubgroupTransport hC e N hN)
        (TopologicalAbelianization.congr
          (residualQuotientConjugationContinuousMulEquiv hC N hN g) a) =
      TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC
          (N.map e.toMulEquiv.toMonoidHom) (subgroupMap_isClosed e N hN) (e g))
        (TopologicalAbelianization.congr
          (residualQuotientSubgroupTransport hC e N hN) a) := by
  obtain ⟨z, rfl⟩ := TopologicalAbelianization.surjective_mk
    (N ⧸ proCResidualCore C N) a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C N) z
  simp only [TopologicalAbelianization.congr_apply_mk,
    residualQuotientConjugationContinuousMulEquiv_apply_mk,
    residualQuotientSubgroupTransport_apply_mk]
  apply congrArg (fun y : N.map e.toMulEquiv.toMonoidHom =>
    TopologicalAbelianization.mk
      (N.map e.toMulEquiv.toMonoidHom ⧸
        proCResidualCore C (N.map e.toMulEquiv.toMonoidHom))
      (QuotientGroup.mk' (proCResidualCore C (N.map e.toMulEquiv.toMonoidHom)) y))
  apply Subtype.ext
  change e (g * (x : G) * g⁻¹) = e g * e (x : G) * (e g)⁻¹
  rw [map_mul, map_mul, map_inv]

/-- Faithfulness of residual abelianized quotient conjugation is preserved
by an ambient continuous group equivalence. -/
theorem residualAbelianizationQuotientConjugation_injective_map_iff
    (hC : FiniteGroupClass.FullFormation C) (e : G ≃ₜ* H)
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    Function.Injective (residualAbelianizationQuotientConjugation hC
      (N.map e.toMulEquiv.toMonoidHom) (subgroupMap_isClosed e N hN)) ↔
      Function.Injective (residualAbelianizationQuotientConjugation hC N hN) := by
  let t : TopologicalAbelianization (N ⧸ proCResidualCore C N) ≃ₜ*
      TopologicalAbelianization
        (N.map e.toMulEquiv.toMonoidHom ⧸
          proCResidualCore C (N.map e.toMulEquiv.toMonoidHom)) :=
    TopologicalAbelianization.congr (residualQuotientSubgroupTransport hC e N hN)
  rw [residualAbelianizationQuotientConjugation_injective_iff hC
    (N.map e.toMulEquiv.toMonoidHom) (subgroupMap_isClosed e N hN),
    residualAbelianizationQuotientConjugation_injective_iff hC N hN]
  constructor
  · intro hfaith g hg htriv
    have hnotmem : e g ∉ N.map e.toMulEquiv.toMonoidHom := by
      intro hmem
      obtain ⟨x, hx, heq⟩ := hmem
      exact hg (e.injective heq ▸ hx)
    apply hfaith (e g) hnotmem
    apply MulEquiv.ext
    intro b
    obtain ⟨a, rfl⟩ := t.surjective b
    have hc := residualAbelianizationSubgroupTransport_conjugation hC e N hN g a
    have ha : TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC N hN g) a = a :=
      DFunLike.congr_fun htriv a
    rw [ha] at hc
    exact hc.symm
  · intro hfaith h hh htriv
    obtain ⟨g, rfl⟩ := e.surjective h
    have hnotmem : g ∉ N := fun hg => hh ⟨g, hg, rfl⟩
    apply hfaith g hnotmem
    apply MulEquiv.ext
    intro a
    apply t.injective
    have hc := residualAbelianizationSubgroupTransport_conjugation hC e N hN g a
    have ha : TopologicalAbelianization.congr
        (residualQuotientConjugationContinuousMulEquiv hC
          (N.map e.toMulEquiv.toMonoidHom) (subgroupMap_isClosed e N hN) (e g))
        (t a) = t a := DFunLike.congr_fun htriv (t a)
    exact hc.trans ha

end ProCGroups.ProC
