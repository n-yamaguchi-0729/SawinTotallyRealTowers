/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.PGroup
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.SetTheory.Cardinal.ToNat
import ProCGroups.FiniteGeneration.Basic
import ProCGroups.FiniteGroups.StandardClasses
import ProCGroups.FreeProC.Basic
import ProCGroups.FreeProC.Construction
import ProCGroups.Generation.Basic
import ProCGroups.ProP.FrattiniPowers
import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.MinimalEpimorphism
import SawinTotallyRealTowers.MaximalRealProPGroup
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.RealProTwoGeneratorRank
import SawinTotallyRealTowers.SixPrimeSupport
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Set.Image
import Mathlib.Data.ZMod.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Order

set_option autoImplicit false

/-!
# A constructed minimal free source for the initial real pro-2 group

The finite-rank free source is an actual completion of an abstract free group.
Its epimorphism to the arithmetic group has kernel in the Frattini subgroup.
-/

namespace ClassFieldTower.Sawin

open ProCGroups ProCGroups.FreeProC ProCGroups.Generation ProCGroups.FiniteGeneration
open ClassFieldTower.ProP

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The constructed free pro-2 group on five generators. -/
noncomputable def sawinFreeProTwoSource :
    EpimorphicallyFreeProCGroupOnConvergingSetData.{0, 0} (FiniteGroupClass.pGroup 2) :=
  finiteFreeProCSource (FiniteGroupClass.pGroup 2)
    (FiniteGroupClass.pGroup_formation 2) (FiniteGroupClass.pGroup_hereditary 2)
    (ULift.{0} (Fin 5))

/-- The actual free source has exactly five basis elements. -/
theorem sawinFreeProTwoSource_basisCard : Cardinal.mk sawinFreeProTwoSource.basis = 5 := by
  change Cardinal.mk (ULift.{0} (Fin 5)) = 5
  simp only [Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin, Nat.cast_ofNat]

/-- The arithmetic group is an actual quotient of a rank-five free pro-2 group
whose kernel lies in the closed power--commutator subgroup. -/
theorem exists_maximalRealProTwo_minimal_free_epimorphism :
    ∃ q : sawinFreeProTwoSource.carrier →ₜ*
      (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
        maximalRealProPOutside 2 sawinRationalPrimeSupport),
      Function.Surjective q ∧
        q.toMonoidHom.ker ≤ closedPowerCommutator 2 sawinFreeProTwoSource.carrier := by
  classical
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    maximalRealProPOutside 2 sawinRationalPrimeSupport
  let G : Type := M ≃ₐ[ℚ] M
  let F : Type := sawinFreeProTwoSource.carrier
  let : IsGalois ℚ M := maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport
  have hG : ProC.HasPGroupOpenNormalBasis 2 G :=
    maximalRealProPOutside_galoisGroup_hasPGroupOpenNormalBasis 2 sawinRationalPrimeSupport
  have hAt : TopologicallyGeneratedByAtMost 5 G := maximalRealProTwo_generatorRank.1
  obtain ⟨q, hq⟩ := exists_finiteFreeProCSource_surjection
    (FiniteGroupClass.pGroup 2) (FiniteGroupClass.pGroup_formation 2)
    (FiniteGroupClass.pGroup_hereditary 2) hG hAt
  have hfgG : TopologicallyFinitelyGenerated G :=
    (topologicallyFinitelyGenerated_iff_exists_topologicallyGeneratedByAtMost).2 ⟨5, hAt⟩
  let eBasis : sawinFreeProTwoSource.basis ≃ Fin 5 :=
    Classical.choice ((Cardinal.mk_eq_nat_iff).mp sawinFreeProTwoSource_basisCard)
  let : Finite sawinFreeProTwoSource.basis := Finite.of_injective eBasis eBasis.injective
  have hfgF : TopologicallyFinitelyGenerated F := by
    let : Fintype sawinFreeProTwoSource.basis := Fintype.ofFinite _
    refine ⟨Finset.univ.image sawinFreeProTwoSource.inclusion, ?_⟩
    simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using
      sawinFreeProTwoSource.isEpimorphicallyFree.generates_range
  have hcyc : ∃ (A : Type) (_ : Group A) (_ : Finite A),
      FiniteGroupClass.pGroup 2 A ∧ IsCyclic A ∧ Nontrivial A := by
    refine ⟨Multiplicative (ZMod 2), inferInstance, inferInstance,
      ⟨inferInstance, ?_⟩, inferInstance, inferInstance⟩
    exact IsPGroup.of_card (n := 1) (by
      simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, pow_one])
  have hFcard : topologicalRank F = 5 :=
    (basisCard_eq_topologicalRank_of_finiteBasis
      (FiniteGroupClass.pGroup 2) (FiniteGroupClass.pGroup_formation 2).quotientClosed
      hcyc sawinFreeProTwoSource).symm.trans sawinFreeProTwoSource_basisCard
  have hFrank : topologicalGeneratorRank F = 5 := by
    change Cardinal.toNat (topologicalRank F) = 5
    rw [hFcard]
    exact Cardinal.toNat_ofNat 5
  refine ⟨q, hq, ?_⟩
  exact ker_le_closedPowerCommutator_of_generatorRank_eq 2
    sawinFreeProTwoSource.isEpimorphicallyFree.hasOpenNormalBasisInClass hG
    hfgF hfgG q hq (hFrank.trans maximalRealProTwo_generatorRank.2.symm)

end ClassFieldTower.Sawin
