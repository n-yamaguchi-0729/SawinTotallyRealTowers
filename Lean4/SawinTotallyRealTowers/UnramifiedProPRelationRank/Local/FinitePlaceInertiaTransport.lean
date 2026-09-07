import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceAlgebraicLocalizationAlgClosure
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalUnramifiedH2Vanishing
import ValuedFieldTheory.Ramification.HilbertRamification.ValuationInertiaAlgEquiv
import ValuedFieldTheory.LocalField.GroupTheory.ContinuousQuotientEquiv

set_option autoImplicit false
/-!
# Finite-place inertia under the local absolute-Galois comparison

The chosen topological comparison from a number-field decomposition group to
the absolute Galois group of its completion preserves inertia.  Consequently
it descends to a topological equivalence of the corresponding unramified
quotients.
-/

open NumberField IsDedekindDomain
open scoped NNReal NumberField ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open RamificationTheory

private theorem fieldAlgebra_isTorsionFree_forInertiaTransport
    {K L : Type*} [Field K] [Field L] [Algebra K L] :
    Module.IsTorsionFree K L :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h ↦ by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · exact Or.inl ((algebraMap K L).injective (by simpa using hr))
    · exact Or.inr hx

/-- In characteristic zero the algebraic closure is canonically identified
with its separable part. -/
noncomputable def algebraicClosureAlgEquivSeparableClosure
    (K : Type) [Field K] [CharZero K] :
    AlgebraicClosure K ≃ₐ[K] SeparableClosure K := by
  let h : separableClosure K (AlgebraicClosure K) = ⊤ :=
    (separableClosure.eq_top_iff K (AlgebraicClosure K)).2 inferInstance
  exact
    ((IntermediateField.equivOfEq h).trans
      (IntermediateField.topEquiv :
        (⊤ : IntermediateField K (AlgebraicClosure K)) ≃ₐ[K]
          AlgebraicClosure K)).symm

/-- The canonical algebraic-to-separable-closure comparison induces the
standard restriction equivalence on absolute Galois groups. -/
theorem autCongr_algebraicClosureAlgEquivSeparableClosure
    (K : Type) [Field K] [CharZero K] :
    AlgEquiv.autCongr (algebraicClosureAlgEquivSeparableClosure K) =
      RamificationTheory.Field.absoluteGaloisGroup.separableClosureMulEquiv K := by
  ext sigma x
  rfl

/-- The algebraic-localization comparison carries the inertia selected by the
original absolute value to the ambient inertia subgroup of the localization. -/
theorem decompositionGroupEquivAlgebraicLocalizationAut_mem_inertia_iff
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (sigma : HilbertRamification.absoluteValueDecompositionGroup K w.1) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut
          vK.Completion
          (HilbertRamification.algebraicLocalizationValuationSubring vK w hw) ↔
      HilbertRamification.localizationRamificationGroups_absoluteValueDecompositionGroupEquiv
          vK hvK w hw sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
          (HilbertRamification.absoluteValueExtensionValuationSubring vK w hw) := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let sigmaGlobal :=
    HilbertRamification.localizationRamificationGroups_absoluteValueDecompositionGroupEquiv
      vK hvK w hw sigma
  let sigmaLocal :=
    HilbertRamification.localizationRamificationGroups_valuationDecompositionGroupEquiv
      vK hvK w hw sigmaGlobal
  have hsigmaLocal :
      ((sigmaLocal :
          RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
            vK.Completion
            (HilbertRamification.algebraicLocalizationValuationSubring vK w hw)) :
          AbsoluteValue.algebraicLocalization vK w.1 w.2 ≃ₐ[vK.Completion]
            AbsoluteValue.algebraicLocalization vK w.1 w.2) =
        decompositionGroupEquivAlgebraicLocalizationAut vK hvK w sigma := by
    rfl
  rw [← HilbertRamification.localizationRamificationGroups_valuationDecompositionGroupEquiv_mem_inertia_iff
    vK hvK w hw sigmaGlobal]
  constructor
  · rintro ⟨tau, htau, htau_eq⟩
    have hlocal : sigmaLocal ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup
          vK.Completion
          (HilbertRamification.algebraicLocalizationValuationSubring vK w hw) := by
      have htau_eq' : tau = sigmaLocal := by
        apply Subtype.ext
        rw [hsigmaLocal]
        exact htau_eq
      rw [← htau_eq']
      exact htau
    exact hlocal
  · intro hlocal
    refine ⟨sigmaLocal, hlocal, ?_⟩
    exact hsigmaLocal

/-- Transporting an extension of the intrinsic local valuation across an
algebra equivalence to the separable closure gives the valuation subring used
by local class field theory. -/
theorem localSeparableValuationSubring_eq_comap_algEquiv
    (K : Type) (L : Type*) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (e : L ≃ₐ[K] SeparableClosure K) :
    localSeparableValuationSubring K =
      (ValuativeRel.valuation L).valuationSubring.comap e.symm.toRingHom := by
  let B : ValuationSubring (SeparableClosure K) :=
    (ValuativeRel.valuation L).valuationSubring.comap e.symm.toRingHom
  let _ : (localCompleteDVF K).valuation.HasExtension B.valuation :=
    ValuationTheory.DiscreteValuationField.Valuation.hasExtension_valuation_of_valuationSubring_pullback
      (localCompleteDVF K).valuation B fun x ↦ by
        change (ValuativeRel.valuation L) (e.symm (algebraMap K (SeparableClosure K) x)) ≤ 1 ↔
          (localCompleteDVF K).valuation x ≤ 1
        rw [e.symm.commutes]
        exact Valuation.HasExtension.val_map_le_one_iff
          (ValuativeRel.valuation K) (ValuativeRel.valuation L) x
  exact localSeparableValuationSubring_eq_of_hasExtension K B

/-- The absolute-value valuation subring on an algebraic localization is the
valuation subring of its norm-induced valuation. -/
theorem algebraicLocalizationValuationSubring_eq_normValuationSubring
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (vK : AbsoluteValue K ℝ) (w : AbsoluteValueExtension vK L)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1) :
    letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
    letI : SMul K w.1.Completion := hK.toSMul
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    letI : Valued (AbsoluteValue.algebraicLocalization vK w.1 w.2) NNReal :=
      localizedCompletionFinitePlaceValued vK w hvKna
    letI : ValuativeRel (AbsoluteValue.algebraicLocalization vK w.1 w.2) :=
      localizedCompletionFinitePlaceValuativeRel vK w hvKna
    HilbertRamification.algebraicLocalizationValuationSubring vK w hw =
      (ValuativeRel.valuation
        (AbsoluteValue.algebraicLocalization vK w.1 w.2)).valuationSubring := by
  let hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  let _ : SMul K w.1.Completion := hK.toSMul
  let _ := AbsoluteValue.completionAlgebra vK w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vK w.1 w.2
  let _ : Valued E NNReal :=
    localizedCompletionFinitePlaceValued vK w hvKna
  let _ : ValuativeRel E :=
    localizedCompletionFinitePlaceValuativeRel vK w hvKna
  ext x
  rw [mem_absoluteValueValuationSubring_iff]
  change ‖x‖ ≤ 1 ↔
    x ∈ (ValuativeRel.valuation E).valuationSubring
  rw [← localizedCompletion_mem_integers_iff_norm_le_one vK w hvKna]
  rw [Valuation.mem_integer_iff, Valuation.mem_valuationSubring_iff]

/-- The norm-induced valuation on a number-field finite-place completion is
the valuation of a nonarchimedean local field. -/
theorem finitePlaceNormCompletionIsNonarchimedeanLocalField
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    @IsNonarchimedeanLocalField vF.Completion inferInstance
      (finitePlaceCompletionValuativeRel vF
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v))
      inferInstance := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna :=
    NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let _ : IsUltrametricDist vF.Completion :=
    completionIsUltrametricDist vF hvFna
  let _ : NontriviallyNormedField vF.Completion :=
    absoluteValueExtension_completionNontriviallyNormedField vF
      (RayClass.adicAbv_isNontrivial v)
  let _ : LocallyCompactSpace vF.Completion :=
    AbsoluteValue.Completion.locallyCompactSpace
      (finitePlaceCompletionBaseMap_isometry v)
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let nu : Valuation vF.Completion NNReal := Valued.v
  let _ : nu.IsNontrivial :=
    (inferInstance :
      (NormedField.valuation (K := vF.Completion)).IsNontrivial)
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : nu.Compatible := Valuation.Compatible.ofValuation nu
  let _ : ValuativeRel.IsNontrivial vF.Completion :=
    (ValuativeRel.isNontrivial_iff_isNontrivial nu).2 inferInstance
  let _ : IsValuativeTopology vF.Completion :=
    isValuativeTopology_of_valued_ofValuation vF.Completion NNReal
  exact
    { toIsValuativeTopology := inferInstance
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := inferInstance }

/-- The selected algebraic localization at a finite place is compared
directly with the separable closure of the completed field. -/
noncomputable def finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let w := finitePlaceAbsoluteValueExtension F v
    letI hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
    letI : SMul F w.1.Completion := hF.toSMul
    letI := AbsoluteValue.completionAlgebra vF w.1 w.2
    AbsoluteValue.algebraicLocalization vF w.1 w.2 ≃ₐ[vF.Completion]
      SeparableClosure vF.Completion := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let w := finitePlaceAbsoluteValueExtension F v
  letI hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
  letI : SMul F w.1.Completion := hF.toSMul
  letI := AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vF w.1 w.2
  letI : CharZero vF.Completion :=
    charZero_of_injective_algebraMap
      (algebraMap F vF.Completion).injective
  exact
    (absoluteValueAlgebraicLocalizationAlgEquivAlgebraicClosure
      vF (RayClass.adicAbv_isNontrivial v)
        (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v) w).trans
      (algebraicClosureAlgEquivSeparableClosure vF.Completion)

/-- The selected finite-place decomposition group is compared directly with
the absolute Galois group of the completed field's separable closure. -/
noncomputable def
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceAbsoluteDecompositionGroup F v ≃ₜ*
      Gal(SeparableClosure
        (NumberField.HeightOneSpectrum.adicAbv F v).Completion /
        (NumberField.HeightOneSpectrum.adicAbv F v).Completion) :=
  (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup F v).trans
    (RamificationTheory.Field.absoluteGaloisGroup.separableClosureContinuousMulEquiv
      (NumberField.HeightOneSpectrum.adicAbv F v).Completion)

/-- The kernel of the local residue-degree map is the ambient copy of the
valuation-subring inertia group. -/
theorem localResidueDegree_ker_eq_valuationInertiaGroupInAut
    (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    MonoidHom.ker (localResidueDegree K).toMonoidHom =
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K
        (localSeparableValuationSubring K) := by
  rw [localResidueDegree_ker_eq_residueAction_ker]
  let A := localSeparableValuationSubring K
  let hA := localSeparableDecompositionGroup_eq_top K
  ext sigma
  change residueAlgActionOfEqTop K A hA sigma = 1 ↔
    sigma ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut K A
  constructor
  · intro hsigma
    let tau := toDecompositionGroupOfEqTop K A hA sigma
    have htau : tau ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K A := by
      rw [← RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction_ker]
      exact hsigma
    exact ⟨tau, htau, rfl⟩
  · rintro ⟨tau, htau, htau_sigma⟩
    change
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction
          (K := K) A (toDecompositionGroupOfEqTop K A hA sigma) = 1
    have htau_ker :
        RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction
            (K := K) A tau = 1 := by
      rw [← MonoidHom.mem_ker,
        RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction_ker]
      exact htau
    have htau_eq : tau = toDecompositionGroupOfEqTop K A hA sigma := by
      apply Subtype.ext
      exact htau_sigma
    rw [← htau_eq]
    exact htau_ker

/-- The B17 finite-place comparison followed by restriction to the separable
closure is conjugation by the corresponding composite algebra equivalence. -/
theorem finitePlaceDecompositionTransport_apply
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let w := finitePlaceAbsoluteValueExtension F v
    letI hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
    letI : SMul F w.1.Completion := hF.toSMul
    letI := AbsoluteValue.completionAlgebra vF w.1 w.2
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
        F v sigma =
      AlgEquiv.autCongr
        (finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v)
        (decompositionGroupEquivAlgebraicLocalizationAut
          vF (RayClass.adicAbv_isNontrivial v) w sigma) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let w := finitePlaceAbsoluteValueExtension F v
  let hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
  let _ : SMul F w.1.Completion := hF.toSMul
  let _ := AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vF w.1 w.2
  let _ : Module.IsTorsionFree vF.Completion E :=
    fieldAlgebra_isTorsionFree_forInertiaTransport
  let _ : IsAlgClosure vF.Completion E :=
    finitePlaceAlgebraicLocalization_isAlgClosure F v
  let _ : CharZero vF.Completion :=
    charZero_of_injective_algebraMap
      (algebraMap F vF.Completion).injective
  let eEA : E ≃ₐ[vF.Completion] AlgebraicClosure vF.Completion :=
    absoluteValueAlgebraicLocalizationAlgEquivAlgebraicClosure
      vF (RayClass.adicAbv_isNontrivial v) hvFna w
  let eAS : AlgebraicClosure vF.Completion ≃ₐ[vF.Completion]
      SeparableClosure vF.Completion :=
    algebraicClosureAlgEquivSeparableClosure vF.Completion
  change
    RamificationTheory.Field.absoluteGaloisGroup.separableClosureMulEquiv
        vF.Completion
        (AlgEquiv.autCongr eEA
          (decompositionGroupEquivAlgebraicLocalizationAut
            vF (RayClass.adicAbv_isNontrivial v) w sigma)) =
      AlgEquiv.autCongr (eEA.trans eAS)
        (decompositionGroupEquivAlgebraicLocalizationAut
          vF (RayClass.adicAbv_isNontrivial v) w sigma)
  rw [← autCongr_algebraicClosureAlgEquivSeparableClosure]
  exact DFunLike.congr_fun (AlgEquiv.autCongr_trans eEA eAS)
    (decompositionGroupEquivAlgebraicLocalizationAut
      vF (RayClass.adicAbv_isNontrivial v) w sigma)

/-- The chosen finite-place comparison detects exactly the original absolute
inertia elements. -/
theorem finitePlaceDecompositionTransport_mem_inertia_iff
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    letI : Valued vF.Completion NNReal :=
      finitePlaceCompletionValued vF hvFna
    letI : ValuativeRel vF.Completion :=
      finitePlaceCompletionValuativeRel vF hvFna
    letI : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut
          vF.Completion (localSeparableValuationSubring vF.Completion) ↔
      finitePlaceAbsoluteDecompositionValuationEquiv F v sigma ∈
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup F
          (finitePlaceAbsoluteValuationSubring F v) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let w := finitePlaceAbsoluteValueExtension F v
  let hw := finitePlaceAbsoluteValueExtension_nonarchimedean F v
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  let hF := AbsoluteValue.extensionCompletionAlgebra (K := F) w.1
  let _ : SMul F w.1.Completion := hF.toSMul
  let _ := AbsoluteValue.completionAlgebra vF w.1 w.2
  let E := AbsoluteValue.algebraicLocalization vF w.1 w.2
  let _ : Module.IsTorsionFree vF.Completion E :=
    fieldAlgebra_isTorsionFree_forInertiaTransport
  let _ : IsAlgClosure vF.Completion E :=
    finitePlaceAlgebraicLocalization_isAlgClosure F v
  let _ : Normal vF.Completion E := IsAlgClosure.normal _ _
  let _ : CharZero vF.Completion :=
    charZero_of_injective_algebraMap
      (algebraMap F vF.Completion).injective
  let _ : Normal vF.Completion (SeparableClosure vF.Completion) :=
    inferInstance
  let _ : Valued E NNReal :=
    localizedCompletionFinitePlaceValued vF w hvFna
  let _ : ValuativeRel E :=
    localizedCompletionFinitePlaceValuativeRel vF w hvFna
  let _ : (ValuativeRel.valuation vF.Completion).HasExtension
      (ValuativeRel.valuation E) :=
    localizedCompletionValuationHasExtension vF w hvFna
  let e : E ≃ₐ[vF.Completion] SeparableClosure vF.Completion :=
    finitePlaceAlgebraicLocalizationAlgEquivSeparableClosure F v
  let A : ValuationSubring E :=
    HilbertRamification.algebraicLocalizationValuationSubring vF w hw
  let B : ValuationSubring (SeparableClosure vF.Completion) :=
    localSeparableValuationSubring vF.Completion
  have hA : A = (ValuativeRel.valuation E).valuationSubring :=
    algebraicLocalizationValuationSubring_eq_normValuationSubring
      vF w hvFna hw
  have hBA : B.comap e.toRingHom = A := by
    change (localSeparableValuationSubring vF.Completion).comap e.toRingHom = A
    rw [localSeparableValuationSubring_eq_comap_algEquiv
      vF.Completion E e, hA]
    ext x
    change e.symm (e x) ∈ (ValuativeRel.valuation E).valuationSubring ↔
      x ∈ (ValuativeRel.valuation E).valuationSubring
    rw [e.symm_apply_apply]
  let d := decompositionGroupEquivAlgebraicLocalizationAut
    vF (RayClass.adicAbv_isNontrivial v) w
  let localEquiv :=
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v
  let eMul := localEquiv.toMulEquiv
  let J : Subgroup Gal(SeparableClosure vF.Completion / vF.Completion) :=
    RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut
      vF.Completion (localSeparableValuationSubring vF.Completion)
  have htransport (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
      eMul sigma = AlgEquiv.autCongr e (d sigma) :=
    finitePlaceDecompositionTransport_apply F v sigma
  have hmem (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
      eMul sigma ∈ J ↔
        finitePlaceAbsoluteDecompositionValuationEquiv F v sigma ∈
          RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup F
            (finitePlaceAbsoluteValuationSubring F v) := by
    rw [htransport sigma]
    have hcongr :=
      autCongr_mem_valuationInertiaGroupInAut_iff e B (d sigma)
    rw [hBA] at hcongr
    rw [hcongr]
    exact decompositionGroupEquivAlgebraicLocalizationAut_mem_inertia_iff
      vF (RayClass.adicAbv_isNontrivial v) w hw sigma
  exact hmem sigma

/-- Pulling local inertia back through the chosen finite-place comparison
recovers the original absolute inertia subgroup. -/
theorem finitePlaceLocalInertia_comap_eq_absoluteInertia
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    letI : Valued vF.Completion NNReal :=
      finitePlaceCompletionValued vF hvFna
    letI : ValuativeRel vF.Completion :=
      finitePlaceCompletionValuativeRel vF hvFna
    letI : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    Subgroup.comap
        (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v).toMonoidHom
        (RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut
          vF.Completion (localSeparableValuationSubring vF.Completion)) =
      finitePlaceAbsoluteInertiaSubgroup F v := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  ext sigma
  exact finitePlaceDecompositionTransport_mem_inertia_iff F v sigma

/-- The direct local absolute-Galois comparison carries finite-place inertia
onto the kernel of the local residue-degree map. -/
theorem finitePlaceAbsoluteInertia_map_eq_localResidueDegree_ker
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    letI : Valued vF.Completion NNReal :=
      finitePlaceCompletionValued vF hvFna
    letI : ValuativeRel vF.Completion :=
      finitePlaceCompletionValuativeRel vF hvFna
    letI : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    Subgroup.map
        (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v).toMonoidHom
        (finitePlaceAbsoluteInertiaSubgroup F v) =
      MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  let localEquiv :=
    finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup F v
  let eMul := localEquiv.toMulEquiv
  let J : Subgroup Gal(SeparableClosure vF.Completion / vF.Completion) :=
    RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut
      vF.Completion (localSeparableValuationSubring vF.Completion)
  have hcomap :
      Subgroup.comap eMul.toMonoidHom J =
        finitePlaceAbsoluteInertiaSubgroup F v :=
    finitePlaceLocalInertia_comap_eq_absoluteInertia F v
  have hmap :
      Subgroup.map eMul.toMonoidHom
          (finitePlaceAbsoluteInertiaSubgroup F v) = J := by
    rw [← hcomap]
    exact Subgroup.map_comap_eq_self_of_surjective eMul.surjective J
  change Subgroup.map eMul.toMonoidHom
      (finitePlaceAbsoluteInertiaSubgroup F v) =
    MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom
  calc
    Subgroup.map eMul.toMonoidHom
        (finitePlaceAbsoluteInertiaSubgroup F v) = J := hmap
    _ = MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom := by
      change
        RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroupInAut
            vF.Completion (localSeparableValuationSubring vF.Completion) =
          MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom
      exact
        (localResidueDegree_ker_eq_valuationInertiaGroupInAut
          vF.Completion).symm

/-- The unramified quotient of a finite-place decomposition group is the
standard local unramified Galois quotient. -/
noncomputable def finitePlaceUnramifiedQuotientContinuousMulEquiv
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    letI : Valued vF.Completion NNReal :=
      finitePlaceCompletionValued vF hvFna
    letI : ValuativeRel vF.Completion :=
      finitePlaceCompletionValuativeRel vF hvFna
    letI : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    finitePlaceAbsoluteDecompositionGroup F v ⧸
        finitePlaceAbsoluteInertiaSubgroup F v ≃ₜ*
      LocalUnramifiedGaloisQuotient vF.Completion := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  letI : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  letI : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  letI : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  exact
    LocalFieldTheory.QuotientGroup.continuousCongr
      (finitePlaceAbsoluteInertiaSubgroup F v)
      (MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom)
      (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
        F v)
      (finitePlaceAbsoluteInertia_map_eq_localResidueDegree_ker F v)

@[simp]
theorem finitePlaceUnramifiedQuotientContinuousMulEquiv_mk
    (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F))
    (sigma : finitePlaceAbsoluteDecompositionGroup F v) :
    let vF := NumberField.HeightOneSpectrum.adicAbv F v
    let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
    letI : Valued vF.Completion NNReal :=
      finitePlaceCompletionValued vF hvFna
    letI : ValuativeRel vF.Completion :=
      finitePlaceCompletionValuativeRel vF hvFna
    letI : IsNonarchimedeanLocalField vF.Completion :=
      finitePlaceNormCompletionIsNonarchimedeanLocalField F v
    finitePlaceUnramifiedQuotientContinuousMulEquiv F v
        (QuotientGroup.mk' (finitePlaceAbsoluteInertiaSubgroup F v) sigma) =
      QuotientGroup.mk'
        (MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom)
        (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
          F v sigma) := by
  let vF := NumberField.HeightOneSpectrum.adicAbv F v
  let hvFna := NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv F v
  let _ : Valued vF.Completion NNReal :=
    finitePlaceCompletionValued vF hvFna
  let _ : ValuativeRel vF.Completion :=
    finitePlaceCompletionValuativeRel vF hvFna
  let _ : IsNonarchimedeanLocalField vF.Completion :=
    finitePlaceNormCompletionIsNonarchimedeanLocalField F v
  exact LocalFieldTheory.QuotientGroup.continuousCongr_mk
    (finitePlaceAbsoluteInertiaSubgroup F v)
    (MonoidHom.ker (localResidueDegree vF.Completion).toMonoidHom)
    (finitePlaceDecompositionGroupContinuousMulEquivSeparableAbsoluteGaloisGroup
      F v)
    (finitePlaceAbsoluteInertia_map_eq_localResidueDegree_ker F v) sigma

end ClassFieldTower.Martinet.Shafarevich
