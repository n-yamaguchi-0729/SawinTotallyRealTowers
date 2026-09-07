import ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import ClassFieldTheory.LubinTate.FormalModule.Series
import ClassFieldTheory.LubinTate.FormalModule.LinearTerm
import ClassFieldTheory.LubinTate.FormalModule.Intertwiner
import ClassFieldTheory.LubinTate.FormalModule.CoefficientEquation
import ClassFieldTheory.LubinTate.FormalModule.Reduction
import ClassFieldTheory.LubinTate.FormalModule.StandardSeries
import ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
import ClassFieldTheory.LubinTate.FormalModule.RecursiveCorrection
import ClassFieldTheory.LubinTate.FormalModule.DegreeStabilization
import ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner
import ClassFieldTheory.LubinTate.FormalModule.StandardFormalGroup
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.DefectCorrection
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.IntertwinerConstruction
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarCompatibility
import ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.ScalarEndomorphisms
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardCompositum
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFixedField
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardFrobenius
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardResidue
import ClassFieldTheory.LubinTate.Padic.CompletedChangedStandardUnramified
import ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerFixedField
import ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerPrimitive
import ClassFieldTheory.LubinTate.Padic.CompletedChangedUniformizerThetaFixed
import ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusEvaluation
import ClassFieldTheory.LubinTate.Padic.CompletedFrobeniusLift
import ClassFieldTheory.LubinTate.Padic.CompletedLevel
import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveAction
import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveIrreducible
import ClassFieldTheory.LubinTate.Padic.CompletedPrimitiveUniformizer
import ClassFieldTheory.LubinTate.Padic.CompletedResidueFrobenius
import ClassFieldTheory.LubinTate.Padic.CompletedStandardLevelTransport
import ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedField
import ClassFieldTheory.LubinTate.Padic.CompletedUnramifiedFrobeniusFixed
import ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.Core
import ClassFieldTheory.LubinTate.Padic.MultiplicativeIntertwiner
import ClassFieldTheory.LubinTate.Padic.MultiplicativeSeries
import ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
import ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
import ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
import ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
import ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
import ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
import ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
import ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
import ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
import ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
import ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
import ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
import ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
import ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
import ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
import ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
import ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
import ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
import ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
import ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
import ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
import ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification
import ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
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
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormIndex
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.NormSubgroup
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LubinTateTransport
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.LaurentPrincipalUnitTransport
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedUpperRamification
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicTransportedLevelTower
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormIndex
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardSubgroupIndex
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.StandardNormSubgroupExact
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.TransportedNormSubgroupExact
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.PadicMultiplicativeArtinComparison
import ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.EqualCharacteristicUpperFiltration
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.StandardSubgroupIntersection
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupSurjectivity
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.OrderReversal
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SeparableUnitsNorm

set_option autoImplicit false

/-!
# Equal-characteristic existence for local class field theory

The explicit Lubin--Tate level over the Laurent-series model is transported
to an arbitrary equal-characteristic local field.  Together with an
unramified extension, it supplies a finite Galois extension whose norm
subgroup lies in any prescribed open finite-index subgroup of `Kˣ`.
-/

noncomputable section

namespace LocalClassFieldTheory

open LocalFieldTheory RamificationTheory CyclicCohomology KummerTheory
open ClassFormation
open LubinTate.EqualCharacteristic

variable (K : Type) [Field K]

section LocalField

variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- A transported equal-characteristic Lubin--Tate level whose norm subgroup
is contained in the prescribed uniformizer/principal-unit subgroup. -/
theorem exists_equalCharacteristicLubinTateFiniteGaloisExtension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : FiniteGaloisSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
  let F := equalCharacteristicTargetLocalField K
  let hKres : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F (n - 1)
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra
      K p ϖ hϖ (n - 1)
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ (n - 1)
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ (n - 1)
  have hLT :
      localNormSubgroup K E ≤
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n := by
    simpa [equalCharacteristicTransportedLubinTateNormSubgroup, F, E] using
      (equalCharacteristicTransportedLubinTateNormSubgroup_le_of_pos
        K p ϖ hϖ n hn)
  exact
    exists_finiteGaloisExtension_normSubgroup_map_le_of_normSubgroup_le
      K E (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n) hLT

/-- The transported Lubin--Tate level retained as a named finite abelian
subextension of the fixed separable closure. -/
noncomputable def
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  letI : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  letI : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  exact
    finiteAbelianAbstractExtensionOfEmbedding K E
      (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E)

/-- The explicit transported Lubin--Tate level is base-linearly equivalent
to the concrete fixed field represented by its named finite abelian
subextension. -/
noncomputable def equalCharacteristicTransportedLubinTateFixedFieldEquiv
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let F := equalCharacteristicTargetLocalField K
    letI : CharP K F.residueCharacteristic :=
      equalCharacteristicTargetResidueCharacteristicCharP K p
    let E := equalCharacteristicLubinTateLevelField F m
    letI : CharP K p := hKp
    letI : Algebra K E :=
      equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
    E ≃ₐ[K]
      abstractFixedField K (SeparableClosure K)
        (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
          K p ϖ hϖ m).field := by
  let F := equalCharacteristicTargetLocalField K
  letI : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  letI : CharP K p := hKp
  letI : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  letI : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  letI : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  have hfixed :
      abstractFixedField K (SeparableClosure K) T.field =
        finiteGaloisFieldRangeOfEmbedding K E i := by
    change
      IntermediateField.fixedField
          (finiteGaloisFieldRangeOfEmbedding K E i).fixingSubgroup =
        finiteGaloisFieldRangeOfEmbedding K E i
    exact
      InfiniteGalois.fixedField_fixingSubgroup
        (finiteGaloisFieldRangeOfEmbedding K E i)
  rw [hfixed]
  exact finiteGaloisFieldRangeEquivOfEmbedding K E i

/-- The named transported Lubin--Tate subextension retains the concrete norm
containment at level `m + 1`. -/
theorem
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (m : ℕ) :
    let T :=
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ m
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)).toAddSubgroup := by
  let F := equalCharacteristicTargetLocalField K
  let : CharP K F.residueCharacteristic :=
    equalCharacteristicTargetResidueCharacteristicCharP K p
  let E := equalCharacteristicLubinTateLevelField F m
  let : CharP K p := hKp
  let : Algebra K E :=
    equalCharacteristicTransportedLubinTateLevelAlgebra K p ϖ hϖ m
  let : FiniteDimensional K E :=
    equalCharacteristicTransportedLubinTateLevel_finiteDimensional
      K p ϖ hϖ m
  let : IsAbelianGalois K E :=
    equalCharacteristicTransportedLubinTateLevel_isAbelianGalois
      K p ϖ hϖ m
  have hLT :
      localNormSubgroup K E ≤
        LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1) := by
    simpa [equalCharacteristicTransportedLubinTateNormSubgroup, F, E] using
      (equalCharacteristicTransportedLubinTateNormSubgroup_le_uniformizerPrincipalSubgroup
        K p ϖ hϖ m)
  let i := AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K E
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ m
  have hmap :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom =
        additiveNormSubgroup K E := by
    simpa [T,
      equalCharacteristicTransportedLubinTateFiniteAbelianSubextension,
      i, F, E] using
      map_finiteAbelianAbstractExtension_normSubgroup_eq K E i
  change
    (T.normSubgroup (intrinsicAbsoluteUnits K)).map
        (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
      (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)).toAddSubgroup
  rw [hmap]
  intro x hx
  change Additive.toMul x ∈ LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 (m + 1)
  apply hLT
  exact hx

/-- The transported equal-characteristic Lubin--Tate level, packaged as a
finite abelian subextension of the fixed separable closure. -/
theorem exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (n : ℕ) (hn : 0 < n) :
    ∃ T : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
  refine
    ⟨equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ (n - 1), ?_⟩
  simpa [Nat.sub_add_cancel hn] using
    (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
      K p ϖ hϖ (n - 1))

/-- The named finite abelian standard compositum: its first factor is the
canonical degree-`d` unramified extension and its second factor is the
transported Lubin--Tate level indexed by `n - 1`, whose norm subgroup uses
the principal-unit level `n`. -/
noncomputable def equalCharacteristicStandardFiniteAbelianCompositum
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (d n : ℕ) (hd : 0 < d) :
    FiniteAbelianSubextension (intrinsicAbstractBase K) :=
  (localFiniteUnramifiedAbelianSubextension K d hd).compositum
    (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ (n - 1))

/-- The concrete fixed field of the named standard compositum is the
compositum of its unramified and transported Lubin--Tate fixed fields. -/
theorem equalCharacteristicStandardFiniteAbelianCompositum_fixedField_eq_sup
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (ϖ : Kˣ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (d n : ℕ) (hd : 0 < d) :
    abstractFixedField K (SeparableClosure K)
        (equalCharacteristicStandardFiniteAbelianCompositum
          K p ϖ hϖ d n hd).field =
      abstractFixedField K (SeparableClosure K)
          (localFiniteUnramifiedAbelianSubextension K d hd).field ⊔
        abstractFixedField K (SeparableClosure K)
          (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
            K p ϖ hϖ (n - 1)).field := by
  simpa [equalCharacteristicStandardFiniteAbelianCompositum] using
    (finiteAbelianSubextension_compositum_fixedField K
      (localFiniteUnramifiedAbelianSubextension K d hd)
      (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
        K p ϖ hϖ (n - 1)))

/-- The ordinary norm subgroup of the named standard compositum is contained
in every overgroup of `⟨ϖ^d⟩ U^n`. -/
theorem
    equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    finiteAbelianNormSubgroup K
        (equalCharacteristicStandardFiniteAbelianCompositum
          K p ϖ hϖ d n hd) ≤
      H := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  let T :=
    equalCharacteristicTransportedLubinTateFiniteAbelianSubextension
      K p ϖ hϖ (n - 1)
  have hUle :
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (unramifiedNormSubgroup K d).toAddSubgroup := by
    simpa [U] using
      localFiniteUnramifiedAbelianSubextension_normSubgroup_map_le
        K d hd
  have hTle :
      (T.normSubgroup (intrinsicAbsoluteUnits K)).map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
        (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup := by
    simpa [T, Nat.sub_add_cancel hn] using
      (equalCharacteristicTransportedLubinTateFiniteAbelianSubextension_normSubgroup_map_le
        K p ϖ hϖ (n - 1))
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  simpa [equalCharacteristicStandardFiniteAbelianCompositum, U, T] using
    (finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP)

/-- The two finite abelian factors of the positive-characteristic standard
construction can be retained explicitly, together with their norm controls
and the native norm containment for their compositum. -/
theorem
    exists_equalCharacteristicStandardFiniteAbelianCompositum_nativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ U T : FiniteAbelianSubextension (intrinsicAbstractBase K),
      (U.normSubgroup (intrinsicAbsoluteUnits K)).map
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
          (unramifiedNormSubgroup K d).toAddSubgroup ∧
        (T.normSubgroup (intrinsicAbsoluteUnits K)).map
            (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).symm.toAddMonoidHom ≤
          (LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ 1 n).toAddSubgroup ∧
        finiteAbelianNormSubgroup K (U.compositum T) ≤ H := by
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  have hP :
      (U.compositum T).normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom :=
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle
  refine ⟨U, T, hUle, hTle, ?_⟩
  exact
    finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
      K (U.compositum T) H hP

/-- A standard subgroup in positive characteristic is dominated by the norm
subgroup of an explicitly assembled finite abelian compositum: an unramified
factor controls the uniformizer exponent and a transported Lubin--Tate factor
controls the principal units. -/
theorem exists_equalCharacteristicStandardFiniteAbelianExtension_normSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      P.normSubgroup (intrinsicAbsoluteUnits K) ≤
        H.toAddSubgroup.map
          (baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)).toAddMonoidHom := by
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteAbelianExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteAbelianExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  refine ⟨U.compositum T, ?_⟩
  exact
    finiteAbelianCompositum_normSubgroup_le_of_standard
      K H ϖ d n hϖ hstandard U T hUle hTle

/-- Native field-facing form of the preceding construction: the represented
finite abelian fixed field has ordinary norm subgroup contained in the
prescribed standard overgroup. -/
theorem exists_equalCharacteristicStandardFiniteAbelianNativeNormSubgroup_le
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Subgroup Kˣ)
    (ϖ : Kˣ) (d n : ℕ)
    (hϖ : _root_.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K
      (Additive.ofMul ϖ) = 1)
    (hd : 0 < d) (hn : 0 < n)
    (hstandard : LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤ H) :
    ∃ P : FiniteAbelianSubextension (intrinsicAbstractBase K),
      finiteAbelianNormSubgroup K P ≤ H := by
  obtain ⟨P, hP⟩ :=
    exists_equalCharacteristicStandardFiniteAbelianExtension_normSubgroup_le
      K p H ϖ d n hϖ hd hn hstandard
  exact
    ⟨P,
      finiteAbelianNormSubgroup_le_of_abstractNormSubgroup_le_map
        K P H hP⟩

/-- In positive characteristic, every ordinary open finite-index subgroup of
`Kˣ` is open for the norm topology. -/
theorem openFiniteIndexSubgroup_isNormOpen_of_charP
    (p : ℕ) [Fact p.Prime] [hKp : CharP K p]
    (H : Subgroup Kˣ) [H.FiniteIndex]
    (hH : IsOpen (H : Set Kˣ)) :
    let A := intrinsicAbsoluteUnits K
    let B := intrinsicAbstractBase K
    let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
    ClassFormation.IsNormOpen A B
      ((H.toAddSubgroup.map e.toAddMonoidHom :
        AddSubgroup (ambientFixedAddSubgroup A B)) :
        Set (ambientFixedAddSubgroup A B)) := by
  let A := intrinsicAbsoluteUnits K
  let B := intrinsicAbstractBase K
  let e := baseUnitsEquivGaloisAmbientFixed K (SeparableClosure K)
  obtain ⟨ϖ, d, n, hϖ, hd, hn, hstandard⟩ :=
    LocalFieldTheory.exists_uniformizerPrincipalSubgroup_le_of_isOpen_finiteIndex
      K H hH
  obtain ⟨U, hUle⟩ :=
    exists_unramifiedFiniteGaloisExtension_normSubgroup_map_le K d hd
  obtain ⟨T, hTle⟩ :=
    exists_equalCharacteristicLubinTateFiniteGaloisExtension_normSubgroup_map_le
      K p ϖ hϖ n hn
  let P := U.compositum T
  have hP :
      P.normSubgroup A ≤ H.toAddSubgroup.map e.toAddMonoidHom := by
    simpa [A, B, e, P] using
      (finiteGaloisCompositum_normSubgroup_le_of_standard
        K H ϖ d n hϖ hstandard U T hUle hTle)
  exact (ClassFormation.normTopology_addSubgroup_isOpen_iff A B
    (H.toAddSubgroup.map e.toAddMonoidHom)).2 ⟨P, hP⟩

/-- In positive characteristic, every ordinary open finite-index subgroup is
the ordinary norm subgroup of a finite abelian subextension. -/
theorem finiteAbelianNormSubgroupMap_surjective_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Surjective (finiteAbelianNormSubgroupMap K) := by
  intro H
  let : H.subgroup.FiniteIndex := H.finiteIndex
  apply exists_finiteAbelianNormSubgroup_eq_of_normOpen K H
  exact openFiniteIndexSubgroup_isNormOpen_of_charP
    K p H.subgroup H.isOpen

/-- Positive-characteristic local existence as an order isomorphism: finite
abelian subextensions correspond to ordinary open finite-index subgroups of
Kˣ with the opposite inclusion order. -/
noncomputable def finiteAbelianNormSubgroupOrderIso_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃o
      (OpenFiniteIndexSubgroup K)ᵒᵈ where
  toEquiv := Equiv.ofBijective (finiteAbelianNormSubgroupMap K)
    ⟨finiteAbelianNormSubgroupMap_injective K,
      finiteAbelianNormSubgroupMap_surjective_of_charP K p⟩
  map_rel_iff' := by
    intro L₁ L₂
    change finiteAbelianNormSubgroup K L₂ ≤
        finiteAbelianNormSubgroup K L₁ ↔ L₁ ≤ L₂
    exact (finiteAbelianSubextension_le_iff_normSubgroup_le K L₁ L₂).symm

/-- Underlying equivalence of positive-characteristic local existence. -/
noncomputable def finiteAbelianNormSubgroupEquiv_of_charP
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    FiniteAbelianSubextension (intrinsicAbstractBase K) ≃
      OpenFiniteIndexSubgroup K :=
  (finiteAbelianNormSubgroupOrderIso_of_charP K p).toEquiv

/-- States the theorem `finiteAbelianNormSubgroupOrderIso_of_charP_apply`. -/
@[simp]
theorem finiteAbelianNormSubgroupOrderIso_of_charP_apply
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (L : FiniteAbelianSubextension (intrinsicAbstractBase K)) :
    finiteAbelianNormSubgroupOrderIso_of_charP K p L =
      finiteAbelianNormSubgroupMap K L := by
  rfl

end LocalField

end LocalClassFieldTheory
