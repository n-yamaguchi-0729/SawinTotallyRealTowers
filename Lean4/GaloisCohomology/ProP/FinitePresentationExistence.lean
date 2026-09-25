/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.ClosedKernelFiniteGeneration
import GaloisCohomology.ProP.PresentationQuotientEquiv
import GaloisCohomology.ProP.TrivialZModP
import ProCGroups.FiniteGeneration.Basic
import ProCGroups.FiniteGroups.Classes
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FreeProC.Basic
import ProCGroups.FreeProC.Construction
import ProCGroups.FreeProC.FiniteBasis
import ProCGroups.FreeProC.FinitelyGenerated
import ProCGroups.Generation.Basic
import ProCGroups.Presentations.Profinite
import ProCGroups.ProC.InverseLimits.Predicates
import ProCGroups.ProP.FrattiniPowers
import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.MinimalEpimorphism
import ProCGroups.ProP.Presentation.Basic
import ProCGroups.ProP.Presentation.Minimal
import ProCGroups.ProP.Presentation.RelationCardinal
import ProCGroups.Topologies.ContinuousMonoidHom
import ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.OfMap
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.SetTheory.Cardinal.ToNat
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ZMod
import Mathlib.Topology.Order

set_option autoImplicit false

/-!
# Constructing finite minimal pro-p presentations

A finitely generated pro-p group with finite-dimensional H² has an actual finite minimal
presentation.  The free source is constructed by completion, its epimorphism is minimal by
equality of generator ranks, and the closed kernel is normally generated using H².
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.FreeProC ProCGroups.Generation ProCGroups.FiniteGeneration
open ProCGroups.Presentations ClassFieldTower.Cohomology

noncomputable section

universe u

/-- Finite generation and finite-dimensional H² supply an actual finite minimal pro-p
presentation, including the free source, quotient map, and finite relator family. -/
theorem hasFiniteMinimalPresentation_of_finiteDimensional_h2
    {p : ℕ} [Fact p.Prime]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProC.HasPGroupOpenNormalBasis p G)
    (hfg : TopologicallyFinitelyGenerated G)
    [FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G 2)] :
    HasFiniteMinimalPresentation p G := by
  classical
  let d : ℕ := topologicalGeneratorRank G
  have hrank_lt : topologicalRank G < Cardinal.aleph0 := by
    obtain ⟨S, hS⟩ := hfg
    exact (topologicalRank_le_mk_of_topologicallyGenerates hS).trans_lt (by
      have hSmk : Cardinal.mk (S : Set G) = (S.card : Cardinal) := Cardinal.mk_coe_finset
      rw [hSmk]
      exact Cardinal.natCast_lt_aleph0)
  have hd : topologicalRank G = (d : Cardinal) :=
    (Cardinal.cast_toNat_of_lt_aleph0 hrank_lt).symm
  have hAt : TopologicallyGeneratedByAtMost d G :=
    topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat hd
  let source : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
      (FiniteGroupClass.pGroup p) :=
    finiteFreeProCSource (FiniteGroupClass.pGroup p)
      (FiniteGroupClass.pGroup_formation p) (FiniteGroupClass.pGroup_hereditary p)
      (ULift.{u} (Fin d))
  let F : Type u := source.carrier
  have hbasis : Cardinal.mk source.basis = d := by
    change Cardinal.mk (ULift.{u} (Fin d)) = d
    simp only [Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin]
  let : Fintype source.basis := Fintype.ofEquiv (Fin d)
    (Classical.choice (Cardinal.mk_eq_nat_iff.mp hbasis)).symm
  have hfgF : TopologicallyFinitelyGenerated F := by
    refine ⟨Finset.univ.image source.inclusion, ?_⟩
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      source.isEpimorphicallyFree.generates_range
  have hcyc : ∃ (A : Type u) (_ : Group A) (_ : Finite A),
      FiniteGroupClass.pGroup p A ∧ IsCyclic A ∧ Nontrivial A := by
    refine ⟨ULift.{u} (Multiplicative (ZMod p)), inferInstance, inferInstance,
      ⟨inferInstance, ?_⟩, ?_, inferInstance⟩
    · exact IsPGroup.of_card (n := 1) (by
        simp only [Nat.card_eq_fintype_card, Fintype.card_ulift,
          Fintype.card_multiplicative, ZMod.card, pow_one])
    · exact (MulEquiv.ulift (α := Multiplicative (ZMod p))).isCyclic.mpr inferInstance
  have hFcard : topologicalRank F = (d : Cardinal) :=
    (basisCard_eq_topologicalRank_of_finiteBasis (FiniteGroupClass.pGroup p)
      (FiniteGroupClass.pGroup_formation p).quotientClosed hcyc source).symm.trans hbasis
  have hFrank : topologicalGeneratorRank F = topologicalGeneratorRank G := by
    change Cardinal.toNat (topologicalRank F) = d
    rw [hFcard, Cardinal.toNat_natCast]
  obtain ⟨q, hq⟩ := exists_finiteFreeProCSource_surjection
    (FiniteGroupClass.pGroup p) (FiniteGroupClass.pGroup_formation p)
    (FiniteGroupClass.pGroup_hereditary p) hG hAt
  let R : ClosedSubgroup F :=
    { toSubgroup := q.toMonoidHom.ker
      isClosed' := ContinuousMonoidHom.isClosed_ker q }
  let : R.Normal := inferInstanceAs q.toMonoidHom.ker.Normal
  have hR : (R : Subgroup F) ≤ closedPowerCommutator p F :=
    ker_le_closedPowerCommutator_of_generatorRank_eq p
      source.isEpimorphicallyFree.hasOpenNormalBasisInClass hG hfgF hfg q hq hFrank
  let : CompactSpace q.toMonoidHom.range :=
    isCompact_iff_compactSpace.mp (isCompact_range q.continuous_toFun)
  let erange : q.toMonoidHom.range ≃ₜ* G :=
    ContinuousMulEquiv.ofBijectiveCompactToT2 (Subgroup.subtype q.toMonoidHom.range)
      continuous_subtype_val ⟨Subtype.coe_injective, by
        intro g
        obtain ⟨f, rfl⟩ := hq g
        exact ⟨⟨q f, ⟨f, rfl⟩⟩, rfl⟩⟩
  let e : (F ⧸ (R : Subgroup F)) ≃ₜ* G :=
    (ContinuousMonoidHom.quotientKerContinuousMulEquivRange q).trans erange
  let eH2 : continuousCohomologyZModPLifted p G 2 ≃ₗ[ZMod p]
      continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2 :=
    continuousCohomologyZModPLiftedLinearEquiv e 2
  let : FiniteDimensional (ZMod p)
      (continuousCohomologyZModPLifted p (F ⧸ (R : Subgroup F)) 2) :=
    FiniteDimensional.of_injective eH2.symm.toLinearMap eH2.symm.injective
  obtain ⟨r, _hr, ρ, hclosure⟩ := exists_closedNormal_generating_family_le_finrank_h2
    source.isEpimorphicallyFree.hasOpenNormalBasisInClass R hR
  have hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup p)
      (CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard source hbasis) := by
    let : Fact (FiniteGroupClass.Variety (FiniteGroupClass.pGroup p)) :=
      ⟨⟨(FiniteGroupClass.pGroup_hereditary p).subgroupClosed,
        (FiniteGroupClass.pGroup_formation p).quotientClosed,
        (FiniteGroupClass.pGroup_formation p).finiteProductClosed⟩⟩
    let : Fact (FiniteGroupClass.IsomClosed (FiniteGroupClass.pGroup p)) :=
      ⟨(FiniteGroupClass.pGroup_formation p).isomClosed⟩
    exact IsEpimorphicallyFreeProCGroupOnConvergingSet.isFreeProCGroup_of_finite
      (FiniteGroupClass.pGroup p)
      (CrowellExactSequence.freeProCChosenULiftFamilyOfBasisCard_isEpimorphicallyFree
        source hbasis)
  let P : FiniteProPPresentation p d r source G :=
    { basisCard := hbasis
      relator := fun i ↦ (ρ i : F)
      isPresentation := ⟨hfree, hG, ⟨q, hq, hclosure.symm⟩⟩ }
  refine ⟨source, d, r, P, ?_⟩
  change P.quotient.toMonoidHom.ker ≤ closedPowerCommutator p F
  rw [P.kernel_eq_closedNormalClosure]
  change closedNormalClosure (Set.range (fun i ↦ (ρ i : F))) ≤ closedPowerCommutator p F
  rw [hclosure]
  exact hR

end

end ClassFieldTower.ProP
