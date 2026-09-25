/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ProP.ProfiniteFrattini
import ProCGroups.ProP.FinitePGroupMaximal
import ProCGroups.ProC.OpenNormalSubgroups.Basic
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import ProCGroups.Profinite.OpenSubgroups
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Order.Atoms

set_option autoImplicit false

/-!
# Detecting the pro-two Frattini subgroup by quadratic quotients

The finite-quotient definition of the profinite Frattini subgroup is
equivalent to intersection over open normal subgroups of index two.
For the reverse inclusion, each maximal subgroup of a finite two-group
quotient pulls back to an actual open normal subgroup of index two.
Finite generation and finiteness of the Frattini quotient are not needed.
-/

universe u v

namespace ClassFieldTower.Sawin

private local instance twoPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem frattini_eq_bot_of_card_two
    (Q : Type v) [Group Q] (hCard : Nat.card Q = 2) : frattini Q = ⊥ := by
  let : Fact (Nat.Prime (Nat.card Q)) := ⟨hCard.symm ▸ Nat.prime_two⟩
  let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp (by
    intro hSubsingleton
    have hOne : Nat.card Q = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hSubsingleton, ⟨1⟩⟩
    exact (by decide : (2 : ℕ) ≠ 1) (hCard.symm.trans hOne))
  have hCoatom : IsCoatom (⊥ : Subgroup Q) := by
    refine ⟨bot_ne_top, fun N hN ↦ ?_⟩
    exact N.eq_bot_or_eq_top_of_prime_card.resolve_left (ne_of_gt hN)
  exact le_antisymm (frattini_le_coatom hCoatom) bot_le

/-- In a group with an open-normal finite two-group basis, the profinite
Frattini subgroup is the intersection of the open normal subgroups of
index two. This does not require the group to be finitely generated. -/
theorem profiniteFrattini_eq_iInf_openNormal_index_two
    (G : Type u) [Group G] [TopologicalSpace G] [ContinuousMul G]
    (hG : ProCGroups.ProC.HasPGroupOpenNormalBasis 2 G) :
    ClassFieldTower.ProP.profiniteFrattini G =
      ⨅ (U : OpenNormalSubgroup G) (_ : (U : Subgroup G).index = 2),
        (U : Subgroup G) := by
  apply le_antisymm
  · refine le_iInf fun U ↦ le_iInf fun hIndex ↦ ?_
    intro x hx
    have hxU := ClassFieldTower.ProP.mem_profiniteFrattini_iff.mp hx U
    rw [frattini_eq_bot_of_card_two (G ⧸ (U : Subgroup G)) hIndex] at hxU
    change QuotientGroup.mk' (U : Subgroup G) x = 1 at hxU
    exact (QuotientGroup.eq_one_iff (N := (U : Subgroup G)) x).mp hxU
  · intro x hx
    apply ClassFieldTower.ProP.mem_profiniteFrattini_iff.mpr
    intro U
    rw [frattini, Order.radical]
    refine Subgroup.mem_iInf.mpr fun N ↦ Subgroup.mem_iInf.mpr fun hN ↦ ?_
    have hQ := ProCGroups.ProC.HasOpenNormalBasisInClass.quotient_mem
      (ProCGroups.FiniteGroupClass.pGroup_formation 2) hG U
    let : Finite (G ⧸ (U : Subgroup G)) := hQ.1
    let Nopen : OpenNormalSubgroup (G ⧸ (U : Subgroup G)) :=
      { toOpenSubgroup := { toSubgroup := N, isOpen' := isOpen_discrete _ }
        isNormal' := ClassFieldTower.ProP.isCoatom_normal_of_isPGroup hQ.2 hN }
    let W : OpenNormalSubgroup G := ProCGroups.OpenNormalSubgroup.comap
      (QuotientGroup.mk' (U : Subgroup G))
      (ProCGroups.ProC.OpenNormalSubgroup.quotientProj U).continuous_toFun Nopen
    have hIndex : (W : Subgroup G).index = 2 := by
      change (N.comap (QuotientGroup.mk' (U : Subgroup G))).index = 2
      rw [N.index_comap_of_surjective (QuotientGroup.mk'_surjective (U : Subgroup G))]
      exact ClassFieldTower.ProP.card_quotient_eq_prime_of_isCoatom_isPGroup hQ.2 hN
    exact Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hx W) hIndex

end ClassFieldTower.Sawin
