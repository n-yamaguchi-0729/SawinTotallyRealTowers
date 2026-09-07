import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
import ValuedFieldTheory.Ramification.LocalField.BaseChange
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.UnitQuotientGalois
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
import ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
import ClassFieldTheory.LubinTate.EqualCharacteristic.Ramification.Core

set_option autoImplicit false

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
