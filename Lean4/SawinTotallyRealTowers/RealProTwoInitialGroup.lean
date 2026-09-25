/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.RealProTwoH2Bound
import SawinTotallyRealTowers.RealProTwoGeneratorRank
import SawinTotallyRealTowers.RealProTwoFrattiniQuotient
import SawinTotallyRealTowers.MaximalRealProPGroup
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.SixPrimeSupport
import GaloisCohomology.ProP.FinitePresentationExistence
import GaloisCohomology.ProP.RelationRankH2
import GaloisCohomology.ProP.TrivialZModP
import ProCGroups.GolodShafarevich.FiniteCriterion
import ProCGroups.FiniteGeneration.Basic
import ProCGroups.Generation.Basic
import ProCGroups.ProP.GeneratorRank
import ProCGroups.ProP.FrattiniPowers
import ProCGroups.ProP.FrattiniQuotient
import ProCGroups.ProP.Presentation.RelationCardinal
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# The initial real pro-two group

The arithmetic H² bound and the constructed five-generator quotient supply
a finite minimal presentation. Its relation rank is at most six, so the
Golod--Shafarevich criterion proves that the actual Galois group is infinite.
-/

open ProCGroups ProCGroups.FiniteGeneration ProCGroups.Generation
open ClassFieldTower.Cohomology ClassFieldTower.ProP

namespace ClassFieldTower.Sawin

private local instance initialPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private local instance initialMaximalIsGalois : IsGalois ℚ (maximalRealProPOutside 2 sawinRationalPrimeSupport) :=
  maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport

private theorem nontrivial_initial :
    Nontrivial (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
      maximalRealProPOutside 2 sawinRationalPrimeSupport) := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    maximalRealProPOutside 2 sawinRationalPrimeSupport
  let G : Type := M ≃ₐ[ℚ] M
  let : (closedPowerCommutator 2 G).Normal := closedPowerCommutator_normal 2 G
  let Q : Type := powerCommutatorQuotient 2 G
  have hCard : Nat.card Q = 32 := maximalRealProTwo_powerCommutatorQuotient_card
  let : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  let : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by omega : 1 < Nat.card Q)
  exact (powerCommutatorQuotientMk_surjective 2 G).nontrivial

/-- The actual initial maximal real pro-two group has five generators, finite H²
of dimension at most six, an actual finite minimal presentation with at most
six relations, a negative Golod--Shafarevich polynomial, and infinitely many elements. -/
theorem sawinInitialProTwoGroup_structure :
    let G : Type := maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
      maximalRealProPOutside 2 sawinRationalPrimeSupport
    topologicalGeneratorRank G = 5 ∧
      FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 G 2) ∧
      Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 G 2) ≤ 6 ∧
      ∃ hP : HasFiniteMinimalPresentation 2 G,
        minimalRelationRank 2 G hP ≤ 6 ∧
        (1 : ℝ) - (topologicalGeneratorRank G : ℝ) * (5 / 12) +
          (minimalRelationRank 2 G hP : ℝ) * (5 / 12) ^ 2 ≤ -1 / 24 ∧
        Infinite G := by
  let G : Type := maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
    maximalRealProPOutside 2 sawinRationalPrimeSupport
  have hH2 := sawinInitialProTwoH2_finiteDimensional_finrank_le
  let : FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 G 2) := hH2.1
  have hfg : TopologicallyFinitelyGenerated G :=
    (topologicallyFinitelyGenerated_iff_exists_topologicallyGeneratedByAtMost).2
      ⟨5, maximalRealProTwo_generatorRank.1⟩
  have hPres : HasFiniteMinimalPresentation 2 G :=
    hasFiniteMinimalPresentation_of_finiteDimensional_h2
      (maximalRealProPOutside_galoisGroup_hasPGroupOpenNormalBasis
        2 sawinRationalPrimeSupport) hfg
  have hr : minimalRelationRank 2 G hPres ≤ 6 := by
    rw [minimalRelationRank_eq_h2Rank hPres, h2Rank_eq_finrank]
    exact hH2.2
  refine ⟨maximalRealProTwo_generatorRank.2, hH2.1, hH2.2, hPres, hr, ?_, ?_⟩
  · rw [maximalRealProTwo_generatorRank.2]
    have hrR : (minimalRelationRank 2 G hPres : ℝ) ≤ 6 := by exact_mod_cast hr
    norm_num only [Nat.cast_ofNat]
    linarith
  · let : Nontrivial G := nontrivial_initial
    apply infinite_of_four_mul_relationRank_le_generatorRank_sq hPres
    rw [maximalRealProTwo_generatorRank.2]
    omega

end ClassFieldTower.Sawin
