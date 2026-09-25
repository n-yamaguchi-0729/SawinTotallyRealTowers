/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.SixPrimeSupport
import SawinTotallyRealTowers.FiniteKummerContinuousKernel
import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.RealProTwoH2AbsoluteKernel
import SawinTotallyRealTowers.RealProPStageRestriction
import SawinTotallyRealTowers.RealProPStageLocalConditions
import SawinTotallyRealTowers.MaximalRealProPGroup
import SawinTotallyRealTowers.SixPrimeFiniteSupport
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerSPlaceCardinality
import GaloisCohomology.ProP.TrivialZModP
import GaloisCohomology.ProP.H2FiniteStageFamily
import GaloisCohomology.ProP.H2InflationRangeCardinality
import GaloisCohomology.ProP.PresentationQuotientEquiv
import GaloisCohomology.ProP.DiscreteH2Comparison
import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false

/-!
# Six-dimensional degree two for the initial real pro-two group

At every actual finite arithmetic stage the field-unit Kummer image has
at most 64 elements. Its kernel is killed by inflation to the constructed
maximal group. Discrete comparison and the finite-stage Galois equivalence
therefore give a surjection from that Kummer image onto the stage inflation
image. Uniform finite-stage cardinality bounds imply finite continuous H²
and dimension at most six, with no cohomological finiteness assumption.
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace ClassFieldTower.Sawin

open ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich ProCGroups ProCGroups.ProC

private theorem natCard_le_range_of_ker_le
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hker : f.ker ≤ g.ker)
    (hg : Function.Surjective g) [Finite f.range] : Nat.card C ≤ Nat.card f.range := by
  let q : A ⧸ f.ker →+ C := QuotientAddGroup.lift f.ker g hker
  have hq : Function.Surjective q :=
    QuotientAddGroup.lift_surjective_of_surjective f.ker g hg hker
  let e := (QuotientAddGroup.quotientKerEquivRange f).symm
  exact Nat.card_le_card_of_surjective (fun x : f.range => q (e x))
    (hq.comp e.surjective)

private theorem initialStage_inflationRange_natCard_le
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup 2)
      (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
        maximalRealProPOutside 2 sawinRationalPrimeSupport)) :
    Nat.card (degreeTwoInflationRange (p := 2) U) ≤ 2 ^ 6 := by
  let T := sawinRationalPrimeSupport
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := maximalRealProPOutside 2 T
  let G : Type := M ≃ₐ[ℚ] M
  let E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    (realProPOpenNormalStage 2 T U.1).val
  let : IsGalois ℚ M := maximalRealProPOutside_isGalois 2 T
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : IsGalois ℚ E.toIntermediateField := E.isGalois
  have hThree : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ T := by
    apply (rationalPrime_mem_sawinRationalPrimeSupport_iff _).mpr
    decide
  have hmu : (primitiveRoots 2 ℚ).Nonempty :=
    ⟨-1, (mem_primitiveRoots (by decide : 0 < 2)).mpr
      (IsPrimitiveRoot.neg_one 0 (by decide))⟩
  let f := (finiteKummerCoefficientH2Map ℚ E (2 : ℕ+) hmu).hom.toAddMonoidHom
  have hfield := finiteKummerCoefficientH2Map_range_finite_natCard_le_of_unramified_outside
    ℚ E sawinFinitePrimeSupport (2 : ℕ+) hmu
    (realProPOpenNormalStage 2 T U.1).property.1
    (by
      intro v hv
      exact finiteRealPExtension_chosenFinitePlaceIsUnramified 2 T
        (realProPOpenNormalStage 2 T U.1) v
        (fun h => hv ((mem_sawinFinitePrimeSupport_iff v).mpr h)))
    (finiteRealPExtension_chosenInfinitePlaceIsUnramified 2 T
      (realProPOpenNormalStage 2 T U.1))
  let : Finite f.range := hfield.1
  let e : (G ⧸ (U.1 : Subgroup G)) ≃ₜ* Gal(E/ℚ) :=
    realProPOpenNormalQuotientContinuousEquivStage 2 T U.1
  let he : continuousCohomologyZModPLifted 2 Gal(E/ℚ) 2 ≃ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 (G ⧸ (U.1 : Subgroup G)) 2 :=
    continuousCohomologyZModPLiftedLinearEquiv e 2
  let dc : continuousCohomologyZModPLifted 2 Gal(E/ℚ) 2 ≃+
      groupCohomology (Rep.trivial ℤ Gal(E/ℚ) (ULift.{0} (ZMod 2))) 2 :=
    discreteContinuousH2AddEquiv (p := 2) (Q := Gal(E/ℚ))
  let I : continuousCohomologyZModPLifted 2 (G ⧸ (U.1 : Subgroup G)) 2 →ₗ[ZMod 2]
      continuousCohomologyZModPLifted 2 G 2 :=
    (continuousCohomologyZModPMapLifted 2
      (OpenNormalSubgroupInClass.quotientProj U) 2).hom.toLinearMap
  have hMap (x : continuousCohomologyZModPLifted 2 Gal(E/ℚ) 2) :
      I (he x) = (continuousCohomologyZModPMapLifted 2
        (realProPOpenNormalStageRestriction 2 T U.1) 2).hom x := by
    let eHom : (G ⧸ (U.1 : Subgroup G)) →ₜ* Gal(E/ℚ) := e
    have hDef : eHom.comp (OpenNormalSubgroupInClass.quotientProj U) =
        realProPOpenNormalStageRestriction 2 T U.1 := by rfl
    have h := continuousCohomologyZModPMapLifted_comp 2 eHom
      (OpenNormalSubgroupInClass.quotientProj U) 2
    rw [hDef] at h
    exact (ConcreteCategory.congr_hom h x).symm
  let g := I.rangeRestrict.toAddMonoidHom.comp
    (he.toAddEquiv.toAddMonoidHom.comp dc.symm.toAddMonoidHom)
  have hg : Function.Surjective g :=
    I.surjective_rangeRestrict.comp (he.surjective.comp dc.symm.surjective)
  have hker : f.ker ≤ g.ker := by
    intro x hx
    have hc : (finiteKummerContinuousH2Map ℚ (2 : ℕ+) E hmu) (dc.symm x) = 0 := by
      change f (dc (dc.symm x)) = 0
      exact (congrArg f (dc.apply_symm_apply x)).trans hx
    have hzero := finiteKummerContinuousH2Map_ker_le_realProPStageInflation_ker
      T hThree U.1 hmu hc
    apply Subtype.ext
    change I (he (dc.symm x)) = 0
    exact (hMap _).trans hzero
  have hcard : Nat.card I.range ≤ Nat.card f.range :=
    natCard_le_range_of_ker_le f g hker hg
  have hfcard : Nat.card f.range ≤ 2 ^ sawinFinitePrimeSupport.card := hfield.2
  rw [sawinFinitePrimeSupport_card] at hfcard
  exact hcard.trans hfcard

/-- The initial maximal real pro-two group has finite continuous H²,
and its dimension over F₂ is at most six. -/
theorem sawinInitialProTwoH2_finiteDimensional_finrank_le :
    FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2
        (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
          maximalRealProPOutside 2 sawinRationalPrimeSupport) 2) ∧
    Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2
        (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
          maximalRealProPOutside 2 sawinRationalPrimeSupport) 2) ≤ 6 := by
  let : IsGalois ℚ (maximalRealProPOutside 2 sawinRationalPrimeSupport) :=
    maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport
  exact finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard 6
    (maximalRealProPOutside_galoisGroup_hasPGroupOpenNormalBasis
      2 sawinRationalPrimeSupport) initialStage_inflationRange_natCard_le

end ClassFieldTower.Sawin
