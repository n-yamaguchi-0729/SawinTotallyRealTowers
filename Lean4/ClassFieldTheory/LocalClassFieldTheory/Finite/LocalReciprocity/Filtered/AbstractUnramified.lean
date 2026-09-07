import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.Unramified
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
import ValuedFieldTheory.LocalField.Analytic.Arithmetic
import ValuedFieldTheory.LocalField.Analytic.ContinuousFieldUnitLog
import ValuedFieldTheory.LocalField.Analytic.DenominatorValuation
import ValuedFieldTheory.LocalField.Analytic.FieldUnitLogExtension
import ValuedFieldTheory.LocalField.Analytic.LogExpAdditivity
import ValuedFieldTheory.LocalField.Analytic.LogExpComposition
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.ExpConvergence
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCore
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoicePositions
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.PowerSeriesComposition
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ProductArgument
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.BasicFactors
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ChoiceCountSystem
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalCoreBase.ExplicitChoiceCounts
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.FormalProduct
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.Homomorphisms
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.LogConvergence
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitExp
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.PrincipalUnitLog
import ValuedFieldTheory.LocalField.Analytic.LogExpSeries.SeriesTerms
import ValuedFieldTheory.LocalField.Analytic.LogExpContinuity
import ValuedFieldTheory.LocalField.Analytic.PrincipalUnitExpLogEquiv
import ValuedFieldTheory.LocalField.Analytic.FieldUnitLogUniqueness
import ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv
import ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup
import ValuedFieldTheory.LocalField.GroupTheory.PowerIndex
import ValuedFieldTheory.LocalField.DiscreteValuationField.Basic
import ValuedFieldTheory.LocalField.DiscreteValuationField.EqualCharacteristicLaurent
import ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicQp
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicField
import ValuedFieldTheory.LocalField.DiscreteValuationField.FiniteCoefficientLaurent
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormBase
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitDecomposition
import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationIdeal
import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationInvariants
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestriction
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CyclicValueGroup
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.SeriesValuationEstimates
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuationUniformizer
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.CompleteRangeRestriction
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.UniformizerIntegerValuation
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.RangeRestrictedTopology
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.LocalFieldRangeRestriction
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuedExtensionUnitMap
import ValuedFieldTheory.LocalField.DiscreteValuationField.WithZeroValuationTopology
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNorm
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldNormEquiv
import ValuedFieldTheory.LocalField.DiscreteValuationField.PolynomialRootProximity
import ValuedFieldTheory.LocalField.DiscreteValuationField.RamificationAddVal
import ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Core
import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.Core
import ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitInverseLimitSurjectivity
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitFactors
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicModuleStructure
import ValuedFieldTheory.LocalField.DiscreteValuationField.MixedCharacteristicStructure.Core
import ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic
import ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
import ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaIndexing
import ValuedFieldTheory.LocalField.DiscreteValuationField.IwasawaPrincipalUnits
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitStructure
import ValuedFieldTheory.LocalField.DiscreteValuationField.PowerIndex
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex
import ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas
import ValuedFieldTheory.LocalField.DiscreteValuationField.Units
import ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup
import ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.AdditiveEquiv
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionTopology
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Norm
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormSubgroupFunctoriality
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormalizedIntegerValuation
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PowerClassFiniteness
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitQuotients
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnits
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ProfiniteUnits
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.MultiplicativeDecomposition
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueUnits
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnramifiedFrobenius
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuedTopology
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
import ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UniformizerPrincipalQuotient
import ValuedFieldTheory.LocalField.Padic.ClosedAddSubgroup
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinRelation
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.Existence
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.IntegralClosure
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.IntegralTranslate
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.PrimeElement
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.RamificationIndex
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.ValuationRingEquiv
import ValuedFieldTheory.LocalField.Padic.Cyclotomic.Unramified.ArithmeticFrobenius
import ClassFieldTheory.LocalFieldTheory.Padic.Cyclotomic.Unramified.CanonicalExtension
import ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField
import ValuedFieldTheory.LocalField.Padic.PrincipalUnits
import ValuedFieldTheory.LocalField.Padic.UnitDecomposition
import ValuedFieldTheory.LocalField.Unramified.BaseChange
import ValuedFieldTheory.LocalField.Unramified.BaseChangeCore
import ValuedFieldTheory.LocalField.Unramified.BasicInvariants
import ValuedFieldTheory.LocalField.Unramified.Composition
import ValuedFieldTheory.LocalField.Unramified.Definitions
import ValuedFieldTheory.LocalField.Unramified.FiniteSupport
import ValuedFieldTheory.LocalField.Unramified.HenselReduction
import ValuedFieldTheory.LocalField.Unramified.HenselianAlgebraicExtension
import ValuedFieldTheory.LocalField.Unramified.MaximalResidue
import ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
import ValuedFieldTheory.LocalField.Unramified.ResidueEmbedding
import ValuedFieldTheory.LocalField.Unramified.ResidueLifting
import ValuedFieldTheory.LocalField.Unramified.Separable
import ValuedFieldTheory.LocalField.NormUnits
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.NormSubgroupOrderEmbedding
import ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormContainment
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Core

set_option autoImplicit false

/-!
# Abstract unramified fixed fields and ramification groups

This file transfers unramifiedness from the residue-degree datum on the
absolute Galois group to the concrete valuation on the corresponding finite
fixed field.  It is the bridge from the canonical abstract unramified
extensions used in finite local reciprocity to the upper ramification groups
used in the Hasse--Arf development.
-/

noncomputable section

namespace LocalClassFieldTheory

open RamificationTheory.LocalField
open LubinTate

open ClassFormation
open CyclicCohomology
open LocalClassFieldTheory
open LocalFieldTheory
open RamificationTheory
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension
open scoped NNReal ValuativeRel

universe u

private theorem baseFixingExtensionSubgroup_index_eq_finrank
    (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (E : IntermediateField K Ω) [FiniteDimensional K E] [IsGalois K E] :
    (extensionSubgroup
      (closedFixingSubgroup K Ω (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup K Ω E)
      (fixingSubgroupLeBase K Ω E)).index =
        Module.finrank K E := by
  let : Finite
      ((closedFixingSubgroup K Ω
          (⊥ : IntermediateField K Ω)).toSubgroup ⧸
        extensionSubgroup
          (closedFixingSubgroup K Ω
            (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup K Ω E)
          (fixingSubgroupLeBase K Ω E)) :=
    Finite.of_equiv (Gal(E / K))
      (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).symm.toEquiv
  calc
    _ = Nat.card
        ((closedFixingSubgroup K Ω
            (⊥ : IntermediateField K Ω)).toSubgroup ⧸
          extensionSubgroup
            (closedFixingSubgroup K Ω
              (⊥ : IntermediateField K Ω))
            (closedFixingSubgroup K Ω E)
            (fixingSubgroupLeBase K Ω E)) :=
      Subgroup.index_eq_card _
    _ = Nat.card (Gal(E / K)) :=
      Nat.card_congr
        (baseFixingExtensionQuotientEquivGaloisGroup K Ω E).toEquiv
    _ = Module.finrank K E :=
      IsGalois.card_aut_eq_finrank K E

/-- For a field finite over the distinguished abstract base, the absolute
residue degree agrees with its relative residue degree over that base. -/
theorem finiteAbstractField_residueDegree_eq_relativeResidueDegree
    {G : Type u} [Group G] [TopologicalSpace G]
    (D : DegreeData G) (H : FiniteAbstractField G) :
    (H.residueDegree D : ℕ) =
      (H.toFiniteAbstractExtension.residueDegree D : ℕ) := by
  apply Nat.cast_injective (R := Cardinal)
  calc
    ((H.residueDegree D : ℕ) : Cardinal) =
        D.residueDegreeCardinal H.field := by
      exact
        (DegreeData.FiniteResidueAbstractField.residueDegreeCardinal_eq_coe
          (H.toFiniteResidueAbstractField D)).symm
    _ =
        (H.toFiniteAbstractExtension.toAbstractExtension
          |>.relativeResidueDegreeCardinal D) := by
      have h :=
        H.toFiniteAbstractExtension.toAbstractExtension
          |>.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D
      have hbase :
          D.residueDegreeCardinal
              H.toFiniteAbstractExtension.toAbstractExtension.base = 1 := by
        change D.residueDegreeCardinal (baseField G) = 1
        exact D.residueDegreeCardinal_baseField
      rw [hbase, mul_one] at h
      exact h.symm
    _ =
        ((H.toFiniteAbstractExtension.residueDegree D : ℕ) : Cardinal) :=
      H.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D

/-- The degree of a normal finite abstract field is the ordinary degree of
its concrete fixed field in the chosen separable closure. -/
theorem finiteAbstractField_degree_eq_abstractFixedField_finrank
    (K : Type) [Field K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal) :
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field hnormal
    (H.toFiniteAbstractExtension.degree : ℕ) =
      Module.finrank K E := by
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K H.field hnormal
  calc
    (H.toFiniteAbstractExtension.degree : ℕ) =
        (extensionSubgroup
          (baseField (Gal(SeparableClosure K / K))) H.field
          (le_baseField H.field)).index :=
      H.toFiniteAbstractExtension.extensionSubgroup_index_eq_degree.symm
    _ = H.field.toSubgroup.index := by
      symm
      rw [← Subgroup.relIndex_top_right]
      rfl
    _ = E.fixingSubgroup.index := by
      exact congrArg Subgroup.index
        (InfiniteGalois.fixingSubgroup_fixedField H.field).symm
    _ = Module.finrank K E :=
      (IntermediateField.finrank_eq_fixingSubgroup_index (SeparableClosure K) E).symm

/-- Abstract unramifiedness of a normal finite fixed field gives actual
unramifiedness for its canonical spectral valuation. -/
theorem abstractFixedField_isUnramifiedValuedExtension
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal)
    (hunramified :
      H.toFiniteAbstractExtension.IsUnramified
        (localResidueDatum K)) :
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field hnormal
    letI : NontriviallyNormedField K :=
      localFieldNontriviallyNormedField K
    letI : IsUltrametricDist K :=
      localFieldIsUltrametricDist K
    letI : CompleteSpace K := inferInstance
    letI : NontriviallyNormedField E :=
      finiteExtensionSpectralNormedField K E
    letI : ValuativeRel E :=
      finiteExtensionSpectralValuativeRel K E
    letI : IsNonarchimedeanLocalField E :=
      finiteExtensionSpectralIsNonarchimedeanLocalField K E
    letI : Valuation.HasExtension
        (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
      finiteExtensionSpectralValuation_hasExtension K E
    letI : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
      localCompleteDVF_integerRing_isIntegralClosure K E
    letI : Module.Finite 𝒪[K] 𝒪[E] :=
      localCompleteDVF_integerRing_moduleFinite K E
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      K E := by
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K H.field hnormal

  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K :=
    localFieldIsUltrametricDist K
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
    localCompleteDVF_integerRing_isIntegralClosure K E
  let : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E

  have hresidueDegree :
      Module.finrank 𝓀[K] 𝓀[E] = Module.finrank K E := by
    calc
      Module.finrank 𝓀[K] 𝓀[E] =
          (H.residueDegree (localResidueDatum K) : ℕ) :=
        (localResidueDatum_residueDegree_eq_residueFinrank K H).symm
      _ =
          (H.toFiniteAbstractExtension.residueDegree
            (localResidueDatum K) : ℕ) :=
        finiteAbstractField_residueDegree_eq_relativeResidueDegree
          (localResidueDatum K) H
      _ = (H.toFiniteAbstractExtension.degree : ℕ) :=
        H.toFiniteAbstractExtension.residueDegree_eq_degree_of_isUnramified
          (localResidueDatum K) hunramified
      _ = Module.finrank K E :=
        finiteAbstractField_degree_eq_abstractFixedField_finrank
          K H hnormal

  have hdegree :=
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
      K E
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  have hdegree' :
      (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K] *
          Module.finrank 𝓀[K] 𝓀[E] =
        Module.finrank K E := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp]
    exact hdegree
  have hpos : 0 < Module.finrank 𝓀[K] 𝓀[E] :=
    Module.finrank_pos
  apply
    LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension.mk
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    (𝓂[E] : Ideal 𝒪[E]).ramificationIdx 𝒪[K] *
        Module.finrank 𝓀[K] 𝓀[E] =
      Module.finrank K E := hdegree'
    _ = Module.finrank 𝓀[K] 𝓀[E] := hresidueDegree.symm
    _ = 1 * Module.finrank 𝓀[K] 𝓀[E] := (one_mul _).symm

/-- Every nonnegative upper ramification group of an abstractly unramified
normal finite fixed field is trivial. -/
theorem localUpperRamificationGroup_abstractFixedField_eq_bot
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (H : FiniteAbstractField
      (Gal(SeparableClosure K / K)))
    (hnormal :
      (extensionSubgroup
        (baseField (Gal(SeparableClosure K / K))) H.field
        (le_baseField H.field)).Normal)
    (hunramified :
      H.toFiniteAbstractExtension.IsUnramified
        (localResidueDatum K))
    (t : ℝ) (ht : 0 ≤ t) :
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field hnormal
    localUpperRamificationGroup K E t = ⊥ := by
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsGalois K E :=
    abstractFixedField_isGalois_of_base_normal K H.field hnormal

  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K :=
    localFieldIsUltrametricDist K
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let : IsIntegralClosure 𝒪[E] 𝒪[K] E :=
    localCompleteDVF_integerRing_isIntegralClosure K E
  let : Module.Finite 𝒪[K] 𝒪[E] :=
    localCompleteDVF_integerRing_moduleFinite K E
  let :
      LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        K E :=
    abstractFixedField_isUnramifiedValuedExtension
      K H hnormal hunramified
  exact
    localUpperRamificationGroup_eq_bot_of_unramifiedValuation
      K E t ht

/-! ## The canonical degree-`d` unramified factor -/

/-- The fixed-field endpoint of the canonical degree-`d` unramified
subextension, bundled as an abstract field finite over the distinguished
base. -/
noncomputable def localFiniteUnramifiedAbstractField
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    FiniteAbstractField (intrinsicAbsoluteGalois K) := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  exact ⟨U.field,
    finiteAbelianSubextension_finite_over_absoluteBase K U⟩

/-- The preceding absolute finite-field package has the subgroup underlying
the canonical finite unramified abelian subextension. -/
@[simp]
theorem localFiniteUnramifiedAbstractField_field
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    (localFiniteUnramifiedAbstractField K d hd).field =
      (localFiniteUnramifiedAbelianSubextension K d hd).field := by
  rfl

/-- The canonical degree-`d` unramified abstract field is normal over the
distinguished base. -/
theorem localFiniteUnramifiedAbstractField_normal
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    (extensionSubgroup
      (baseField (intrinsicAbsoluteGalois K))
      (localFiniteUnramifiedAbstractField K d hd).field
    (le_baseField
        (localFiniteUnramifiedAbstractField K d hd).field)).Normal := by
  let U := localFiniteUnramifiedAbelianSubextension K d hd
  change
    (extensionSubgroup
      (baseField (intrinsicAbsoluteGalois K)) U.field
      (le_baseField U.field)).Normal
  exact finiteAbelianSubextension_normal_over_absoluteBase K U

/-- The canonical degree-`d` abstract field is unramified for the local
residue degree datum. -/
theorem localFiniteUnramifiedAbstractField_isUnramified
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) :
    (localFiniteUnramifiedAbstractField K d hd).toFiniteAbstractExtension.IsUnramified
      (localResidueDatum K) := by
  let D := localResidueDatum K
  let Bfinite : FiniteAbstractField (intrinsicAbsoluteGalois K) :=
    intrinsicFiniteAbstractBase K
  let Bresidue := Bfinite.toFiniteResidueAbstractField D
  have h :=
    DegreeData.unramifiedExtensionOfDegree_isUnramified
      D Bresidue d hd
  have hbase :
      intrinsicAbstractBase K =
        baseField (intrinsicAbsoluteGalois K) :=
    closedFixingSubgroup_bot_eq_baseField K (SeparableClosure K)
  change
    (baseField (intrinsicAbsoluteGalois K)).toSubgroup ⊓
        D.degree.toMonoidHom.ker ≤
      (localFiniteUnramifiedAbelianSubextension K d hd).field.toSubgroup
  intro g hg
  have hgBase : g ∈ Bresidue.field := by
    change g ∈ intrinsicAbstractBase K
    rw [hbase]
    exact hg.1
  have hgField :=
    h ⟨hgBase, hg.2⟩
  simpa [D, Bfinite, Bresidue,
    localFiniteUnramifiedAbelianSubextension,
    DegreeData.finiteUnramifiedAbelianExtension,
    DegreeData.finiteUnramifiedExtension] using hgField

/-- Every nonnegative upper ramification group of the canonical degree-`d`
unramified abelian fixed field is trivial. -/
theorem localUpperRamificationGroup_finiteUnramifiedAbelianExtension_eq_bot
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (t : ℝ) (ht : 0 ≤ t) :
    let H := localFiniteUnramifiedAbstractField K d hd
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsGalois K E :=
      abstractFixedField_isGalois_of_base_normal K H.field
        (localFiniteUnramifiedAbstractField_normal K d hd)
    localUpperRamificationGroup K E t = ⊥ := by
  exact
    localUpperRamificationGroup_abstractFixedField_eq_bot
      K (localFiniteUnramifiedAbstractField K d hd)
        (localFiniteUnramifiedAbstractField_normal K d hd)
        (localFiniteUnramifiedAbstractField_isUnramified K d hd)
        t ht

/-- The real Artin principal-unit step filtration of the canonical
degree-`d` unramified abelian fixed field is trivial at every index. -/
theorem
    artinPrincipalUnitStepGroup_finiteUnramifiedAbelianExtension_eq_bot
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (d : ℕ) (hd : 0 < d) (t : ℝ) :
    let H := localFiniteUnramifiedAbstractField K d hd
    let E :=
      abstractFixedField K (SeparableClosure K) H.field
    letI : FiniteDimensional K E :=
      abstractFixedField_finiteDimensional
        K (SeparableClosure K) H.field H.finite
    letI : IsAbelianGalois K E := by
      change IsAbelianGalois K
        (abstractFixedField K (SeparableClosure K)
          (localFiniteUnramifiedAbelianSubextension K d hd).field)
      exact finiteAbelianSubextension_fixedField_isAbelianGalois K
        (localFiniteUnramifiedAbelianSubextension K d hd)
    artinPrincipalUnitStepGroup K E t = ⊥ := by
  let H := localFiniteUnramifiedAbstractField K d hd
  let E :=
    abstractFixedField K (SeparableClosure K) H.field
  let : FiniteDimensional K E :=
    abstractFixedField_finiteDimensional
      K (SeparableClosure K) H.field H.finite
  let : IsAbelianGalois K E := by
    change IsAbelianGalois K
      (abstractFixedField K (SeparableClosure K)
        (localFiniteUnramifiedAbelianSubextension K d hd).field)
    exact finiteAbelianSubextension_fixedField_isAbelianGalois K
      (localFiniteUnramifiedAbelianSubextension K d hd)

  let : NontriviallyNormedField K :=
    localFieldNontriviallyNormedField K
  let : IsUltrametricDist K :=
    localFieldIsUltrametricDist K
  let : CompleteSpace K := inferInstance
  let : NontriviallyNormedField E :=
    finiteExtensionSpectralNormedField K E
  let : ValuativeRel E :=
    finiteExtensionSpectralValuativeRel K E
  let : IsNonarchimedeanLocalField E :=
    finiteExtensionSpectralIsNonarchimedeanLocalField K E
  let : Valuation.HasExtension
      (ValuativeRel.valuation K) (ValuativeRel.valuation E) :=
    finiteExtensionSpectralValuation_hasExtension K E
  let :
      LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        K E :=
    abstractFixedField_isUnramifiedValuedExtension
      K H
        (localFiniteUnramifiedAbstractField_normal K d hd)
        (localFiniteUnramifiedAbstractField_isUnramified K d hd)
  exact
    artinPrincipalUnitStepGroup_eq_bot_of_unramifiedValuation
      K E t

end LocalClassFieldTheory
