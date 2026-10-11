/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
import Nyll.ValuedFieldTheory.Ramification.LocalField.BaseChange
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core

/-!
# Upper ramification groups on transported equal-characteristic levels

The explicit Lubin--Tate level field is unchanged when its Laurent-series
base algebra is transported to an arbitrary equal-characteristic local
field.  The normalized Laurent equivalence preserves the valuation rings,
so the general base-field transport theorem identifies the two upper
ramification filtrations.
-/



noncomputable section

open scoped LaurentSeries ValuativeRel

namespace LubinTate

open LocalFieldTheory
open RamificationTheory.LocalField
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.IsNonarchimedeanLocalField
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The two algebra maps from the Laurent model and the target local field
to a transported Lubin--Tate level have the same image. -/
theorem equalCharacteristicTransportedLubinTate_algebraMap_compat
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ)
    (x :
      let F := equalCharacteristicTargetLocalField K
      F.residueField⸨X⸩) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    algebraMap K E
        (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ x) =
      algebraMap B E x := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F n
  let : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  have hcomp :=
    DFunLike.congr_fun
      (equalCharacteristicTransportedLubinTateLevelAlgebra_comp
        K p ϖ hϖ n) x
  simpa using hcomp

/-- Identification of the Galois group over the Laurent base with the
Galois group for the transported target-field algebra.  It leaves every
underlying automorphism of the level field unchanged. -/
noncomputable def equalCharacteristicTransportedLubinTateGaloisEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    Gal(E / B) ≃* Gal(E / K) := by
  let F := equalCharacteristicTargetLocalField K
  let B := F.residueField⸨X⸩
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F n
  letI : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ n
  exact
    galoisGroupEquivOfBaseRingEquiv B K E
      (equalCharacteristicTargetLaurentRingEquiv K p ϖ hϖ)
      (equalCharacteristicTransportedLubinTate_algebraMap_compat
        K p ϖ hϖ n)

@[simp]
theorem equalCharacteristicTransportedLubinTateGaloisEquiv_apply
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ)
    (σ :
      let F := equalCharacteristicTargetLocalField K
      let B := F.residueField⸨X⸩
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      let E := equalCharacteristicLubinTateLevelField F n
      letI : Algebra B E :=
        equalCharacteristicLubinTateLevelAlgebra F n
      Gal(E / B))
    (x :
      let F := equalCharacteristicTargetLocalField K
      letI : CharP K F.residueCharacteristic :=
        equalCharacteristicTargetResidueCharacteristicCharP K p
      equalCharacteristicLubinTateLevelField F n) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p ϖ hϖ n
    equalCharacteristicTransportedLubinTateGaloisEquiv
        K p ϖ hϖ n σ x =
      σ x := by
  rfl

private theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_baseChange
    [Fact
      (equalCharacteristicTargetLocalField K).residueCharacteristic.Prime]
    [CharP K
      (equalCharacteristicTargetLocalField K).residueCharacteristic]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let q := F.residueCharacteristic
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI algBE : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI finBE : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI galBE : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    let upperB :=
      @localUpperRamificationGroup B E
        inferInstance inferInstance
        algBE finBE galBE
        inferInstance inferInstance inferInstance
    letI algKE : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K q ϖ hϖ n
    letI finKE : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K q ϖ hϖ n
    letI galKE : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K q ϖ hϖ n
    let upperK :=
      @localUpperRamificationGroup K E
        inferInstance inferInstance
        algKE finKE galKE
        inferInstance inferInstance inferInstance
    Subgroup.map
        (@galoisGroupEquivOfBaseRingEquiv
          B K E
          inferInstance inferInstance inferInstance
          algBE algKE
          (equalCharacteristicTargetLaurentRingEquiv K q ϖ hϖ)
          (equalCharacteristicTransportedLubinTate_algebraMap_compat
            K q ϖ hϖ n)).toMonoidHom
        (upperB t) =
      upperK t := by
  let F := equalCharacteristicTargetLocalField K
  let q := F.residueCharacteristic
  let B := F.residueField⸨X⸩
  let E := equalCharacteristicLubinTateLevelField F n
  let : ValuativeRel B :=
    equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField B :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let algBE : Algebra B E :=
    equalCharacteristicLubinTateLevelAlgebra F n
  let finBE : FiniteDimensional B E :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  let galBE : IsGalois B E :=
    equalCharacteristicLubinTateLevelField_isGalois F n
  let algKE : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K q ϖ hϖ n
  let finKE : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K q ϖ hϖ n
  let galKE : IsGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isGalois
      K q ϖ hϖ n
  dsimp only
  convert
    @localUpperRamificationGroup_map_baseRingEquiv
      B K E
      inferInstance inferInstance inferInstance
      algBE algKE finBE finKE galBE galKE
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
      (equalCharacteristicTargetLaurentRingEquiv K q ϖ hϖ)
      (equalCharacteristicTransportedLubinTate_algebraMap_compat
        K q ϖ hϖ n)
      (equalCharacteristicTargetLaurentRingEquiv_val_le_one_iff
        K q ϖ hϖ) t using 1

private theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_residueCharacteristic
    [Fact
      (equalCharacteristicTargetLocalField K).residueCharacteristic.Prime]
    [CharP K
      (equalCharacteristicTargetLocalField K).residueCharacteristic]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let q := F.residueCharacteristic
    let B := F.residueField⸨X⸩
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI algBE : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI finBE : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    letI galBE : IsGalois B E :=
      equalCharacteristicLubinTateLevelField_isGalois F n
    let upperB :=
      @localUpperRamificationGroup B E
        (by infer_instance) (by infer_instance)
        algBE finBE galBE
        (by infer_instance) (by infer_instance) (by infer_instance)
    letI algKE : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K q ϖ hϖ n
    letI finKE : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K q ϖ hϖ n
    letI galKE : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K q ϖ hϖ n
    let upperK :=
      @localUpperRamificationGroup K E
        (by infer_instance) (by infer_instance)
        algKE finKE galKE
        (by infer_instance) (by infer_instance) (by infer_instance)
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K q ϖ hϖ n).toMonoidHom
        (upperB t) =
      upperK t := by
  simpa only [equalCharacteristicTransportedLubinTateGaloisEquiv] using
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_baseChange
      K ϖ hϖ n t

/-- The normalized base-field equivalence transports the canonical local
upper ramification group on every explicit Lubin--Tate level. -/
theorem
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (n : ℕ) (t : ℝ) :
    let F := equalCharacteristicTargetLocalField K
    let B := F.residueField⸨X⸩
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F n
    letI : ValuativeRel B :=
      equalCharacteristicLaurentValuativeRel F
    letI : IsNonarchimedeanLocalField B :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    letI : FiniteDimensional B E :=
      equalCharacteristicLubinTateLevelField_finiteDimensional F n
    let upperB := localUpperRamificationGroup B E
    letI : Algebra B E :=
      equalCharacteristicLubinTateLevelAlgebra F n
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra
        K p (hKp := hKp) ϖ hϖ n
    letI : Module K E := Algebra.toModule
    letI : IsGalois K E :=
      equalCharacteristicTransportedLubinTateLevel_isGalois
        K p (hKp := hKp) ϖ hϖ n
    letI : FiniteDimensional K E :=
      equalCharacteristicTransportedLubinTateLevel_finiteDimensional
        K p (hKp := hKp) ϖ hϖ n
    let upperK := localUpperRamificationGroup K E
    Subgroup.map
        (equalCharacteristicTransportedLubinTateGaloisEquiv
          K p (hKp := hKp) ϖ hϖ n).toMonoidHom
        (upperB t) =
      upperK t := by
  let F := equalCharacteristicTargetLocalField K
  have hp : F.residueCharacteristic = p :=
    F.residueCharacteristic_eq_of_charP p
      ((Fact.out : Nat.Prime p).ne_zero)
  subst p
  convert
    equalCharacteristicTransportedLubinTateLocalUpperRamificationGroup_map_eq_residueCharacteristic
      K ϖ hϖ n t using 1

end LubinTate
