/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients
import Nyll.ProCGroups.FiniteGroups.PGroupFormation
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.GroupTheory.PGroup
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Finite p-power characters detect residual abelianized conjugation

A changed continuous cyclic p-power character factors through the actual
maximal pro-p residual quotient. Its change therefore detects conjugation
on the topological abelianization of that quotient.
-/

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC ProCGroups.Abelian

universe u

private theorem cyclicPrimePower_hasOpenNormalBasis (p s : ℕ) [Fact p.Prime] :
    HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)
      (ULift.{u} (Multiplicative (ZMod (p ^ s)))) := by
  have : NeZero (p ^ s) := ⟨pow_ne_zero s (Fact.out : p.Prime).ne_zero⟩
  apply HasOpenNormalBasisInClass.of_finite_discrete
    (FiniteGroupClass.pGroup_formation p).quotientClosed
  refine ⟨inferInstance, IsPGroup.of_card_dvd_pow (n := s) ?_⟩
  have hcard : Nat.card (ULift.{u} (Multiplicative (ZMod (p ^ s)))) = p ^ s := by
    rw [Nat.card_congr (Equiv.ulift : ULift.{u} (Multiplicative (ZMod (p ^ s))) ≃
      Multiplicative (ZMod (p ^ s)))]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rw [hcard]

/-- A changed p-power character detects the actual conjugation automorphism
of the abelianized pro-p residual quotient of a closed normal subgroup. -/
theorem residualAbelianization_conjugation_ne_one_of_cyclicCharacter_ne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (p s : ℕ) [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) (g : G)
    (χ : N →ₜ* Multiplicative (ZMod (p ^ s))) (x : N)
    (hχ : χ (MulAut.conjNormal g x) ≠ χ x) :
    (TopologicalAbelianization.congr
      (residualQuotientConjugationContinuousMulEquiv
        (FiniteGroupClass.pGroup_fullFormation p) N hN g)).toMulEquiv ≠ 1 := by
  have : CompactSpace N := hN.isClosedEmbedding_subtypeVal.compactSpace
  let χup : N →ₜ* ULift.{u} (Multiplicative (ZMod (p ^ s))) :=
    { toMonoidHom := MulEquiv.ulift.symm.toMonoidHom.comp χ.toMonoidHom
      continuous_toFun := continuous_uliftUp.comp χ.continuous_toFun }
  let ψ : N ⧸ proCResidualCore (FiniteGroupClass.pGroup p) N →ₜ*
      ULift.{u} (Multiplicative (ZMod (p ^ s))) :=
    lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary p)
      χup (cyclicPrimePower_hasOpenNormalBasis p s)
  apply KummerTheory.topologicalAbelianization_congr_ne_one_of_character_ne
    (χ := ψ) (x := QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) N) x)
  rw [residualQuotientConjugationContinuousMulEquiv_apply_mk]
  change ψ (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) N)
      (MulAut.conjNormal g x)) ≠
    ψ (QuotientGroup.mk' (proCResidualCore (FiniteGroupClass.pGroup p) N) x)
  simp only [ψ, lift_proCResidualCoreQuotient_mk]
  intro heq
  exact hχ (congrArg ULift.down heq)

end ClassFieldTower.ProP
