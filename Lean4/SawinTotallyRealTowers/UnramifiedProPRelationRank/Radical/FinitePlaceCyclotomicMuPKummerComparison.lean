import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPKummerComparison
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceAlgebraicLocalizationAlgClosure
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicKummerH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FinitePlaceMuPH1Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.LocalValuationKummerDual

set_option autoImplicit false
/-!
# Finite-place comparison of natural and intrinsic-local Kummer H¹

This file compares the restriction of the natural `mu_p` Kummer class to a
finite-place decomposition group with intrinsic Kummer theory over the adic
completion.  The coefficient map uses the actual algebraic-localization
embedding selected by the decomposition--completion equivalence.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open AlgebraicNumberTheory.Valuations
open CategoryTheory ClassFieldTower.Cohomology ClassFieldTower.ProP
open ContRepresentation KummerTheory TopRep

section PowerClassLocalization

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]

/-- Localization of multiplicative power classes from a number field to one
adic completion. -/
noncomputable def finitePlacePowerClassLocalizationMonoidHom
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      ((v.adicCompletion K)ˣ ⧸
        (powMonoidHom p :
          (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range) :=
  QuotientGroup.map
    (powMonoidHom p : Kˣ →* Kˣ).range
    (powMonoidHom p :
      (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom)
    (by
      rintro x ⟨a, rfl⟩
      exact ⟨Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a, by
        rw [powMonoidHom_apply]
        exact (map_pow
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom) a p).symm⟩)

/-- Finite-place localization as a `ZMod p`-linear map on power classes. -/
noncomputable def finitePlacePowerClassLocalization
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    absolutePowerClassModP K p →ₗ[ZMod p]
      FinitePlaceLocalPowerClassModP K p v := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  letI : Module (ZMod p)
      (Additive
        ((v.adicCompletion K)ˣ ⧸
          (powMonoidHom p :
            (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one (v.adicCompletion K) p)
  exact
    (finitePlacePowerClassLocalizationMonoidHom K p v).toAdditive.toZModLinearMap p

/-- A represented global power class localizes to the class of its diagonal
image in the completion. -/
@[simp]
theorem finitePlacePowerClassLocalization_mk
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (a : Kˣ) :
    finitePlacePowerClassLocalization K p v
        (Additive.ofMul
          (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a)) =
      Additive.ofMul
        (QuotientGroup.mk'
          (powMonoidHom p :
            (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)) := by
  rfl

end PowerClassLocalization

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceCyclotomicComparisonFiniteDimensional :
    FiniteDimensional F (FinitePlaceCyclotomicBase F p) :=
  finiteDimensional_idealRadicalCyclotomicBase
    F p (Fact.out : p.Prime)

local instance finitePlaceCyclotomicComparisonNumberField :
    NumberField (FinitePlaceCyclotomicBase F p) :=
  NumberField.of_module_finite F (FinitePlaceCyclotomicBase F p)

local instance finitePlaceCyclotomicComparisonH1Module
    {q : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

private theorem fieldAlgebra_isTorsionFree_forCyclotomicComparison
    {K L : Type} [Field K] [Field L] [Algebra K L] :
    Module.IsTorsionFree K L :=
  Module.IsTorsionFree.of_smul_eq_zero fun r x h ↦ by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · exact Or.inl ((algebraMap K L).injective (by simpa using hr))
    · exact Or.inr hx

private noncomputable def absoluteGaloisSemilinearCongrContinuousMonoidHom
    (K K' : Type) [Field K] [Field K'] (c : K ≃+* K') :
    Field.absoluteGaloisGroup K →ₜ* Field.absoluteGaloisGroup K' := by
  letI : Module.IsTorsionFree K (AlgebraicClosure K) :=
    fieldAlgebra_isTorsionFree_forCyclotomicComparison
  letI : Module.IsTorsionFree K' (AlgebraicClosure K') :=
    fieldAlgebra_isTorsionFree_forCyclotomicComparison
  let e : AlgebraicClosure K ≃+* AlgebraicClosure K' :=
    IsAlgClosure.equivOfEquiv _ _ c
  let conjugate (sigma : Gal(AlgebraicClosure K / K)) :
      Gal(AlgebraicClosure K' / K') :=
    { toRingEquiv := e.symm.trans (sigma.toRingEquiv.trans e)
      commutes' := by
        intro x
        change e (sigma (e.symm (algebraMap K' (AlgebraicClosure K') x))) =
          algebraMap K' (AlgebraicClosure K') x
        rw [IsAlgClosure.equivOfEquiv_symm_algebraMap]
        rw [sigma.commutes]
        rw [IsAlgClosure.equivOfEquiv_algebraMap]
        simp }
  let phi : Gal(AlgebraicClosure K / K) →*
      Gal(AlgebraicClosure K' / K') :=
    { toFun := conjugate
      map_one' := by
        ext x
        exact e.apply_symm_apply x
      map_mul' := by
        intro sigma tau
        ext x
        change e ((sigma * tau) (e.symm x)) =
          e (sigma (e.symm (e (tau (e.symm x)))))
        rw [e.symm_apply_apply]
        rfl }
  exact
    { toMonoidHom := phi
      continuous_toFun :=
        RamificationTheory.Field.absoluteGaloisGroup.semilinear_conjugation_continuous
          c e (IsAlgClosure.equivOfEquiv_algebraMap _ _ c) phi (fun _ ↦ rfl) }

/-- Conjugation between the absolute Galois groups of the two canonical
models of a finite-place completion. -/
noncomputable def finitePlaceCompletionAbsoluteGaloisSemilinearCongr
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Field.absoluteGaloisGroup
        (NumberField.HeightOneSpectrum.adicAbv K v).Completion →ₜ*
      Field.absoluteGaloisGroup (v.adicCompletion K) := by
  let C := (NumberField.HeightOneSpectrum.adicAbv K v).Completion
  let C' := v.adicCompletion K
  let c : C ≃+* C' := (relativeFinitePlaceCompletionAlgEquiv v).toRingEquiv
  exact absoluteGaloisSemilinearCongrContinuousMonoidHom C C' c

/-- The selected decomposition group mapped to the absolute Galois group of
the concrete adic completion. -/
noncomputable def finitePlaceDecompositionToAdicAbsoluteGaloisGroup
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    finitePlaceAbsoluteDecompositionGroup K v →ₜ*
      Field.absoluteGaloisGroup (v.adicCompletion K) :=
  (finitePlaceCompletionAbsoluteGaloisSemilinearCongr K v).comp
    { toMonoidHom :=
        (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup
          K v).toMulEquiv.toMonoidHom
      continuous_toFun :=
        (finitePlaceDecompositionGroupContinuousMulEquivAbsoluteGaloisGroup
          K v).continuous }

private structure FinitePlaceAlgebraicClosureEmbeddingData
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) where
  embedding : AlgebraicClosure K →+* AlgebraicClosure (v.adicCompletion K)
  action : ∀ (sigma : finitePlaceAbsoluteDecompositionGroup K v)
      (x : AlgebraicClosure K),
    absoluteGaloisGroupContinuousMulEquiv
        (v.adicCompletion K)
        (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)
        (embedding x) = embedding (sigma.1 x)
  algebraMap : ∀ x : K,
    embedding (algebraMap K (AlgebraicClosure K) x) =
      algebraMap (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))
        (algebraMap K (v.adicCompletion K) x)

private noncomputable def finitePlaceAlgebraicClosureEmbeddingData
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    FinitePlaceAlgebraicClosureEmbeddingData K v := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let w := finitePlaceAbsoluteValueExtension K v
  letI hK := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
  letI : SMul K w.1.Completion := hK.toSMul
  letI := AbsoluteValue.completionAlgebra vK w.1 w.2
  let c := relativeFinitePlaceCompletionAlgEquiv v
  letI : Module.IsTorsionFree vK.Completion
      (AlgebraicClosure vK.Completion) :=
    fieldAlgebra_isTorsionFree_forCyclotomicComparison
  letI : Module.IsTorsionFree (v.adicCompletion K)
      (AlgebraicClosure (v.adicCompletion K)) :=
    fieldAlgebra_isTorsionFree_forCyclotomicComparison
  let e0 := absoluteValueAlgebraicLocalizationAlgEquivAlgebraicClosure vK
    (RayClass.adicAbv_isNontrivial v)
    (NumberField.HeightOneSpectrum.isNonarchimedean_adicAbv K v) w
  let e1 : AlgebraicClosure vK.Completion ≃+*
      AlgebraicClosure (v.adicCompletion K) :=
    IsAlgClosure.equivOfEquiv _ _ c.toRingEquiv
  let i := AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
  refine
    { embedding := e1.toRingHom.comp (e0.toRingHom.comp i)
      action := ?_
      algebraMap := ?_ }
  · intro sigma x
    change
      e1 ((AlgEquiv.autCongr e0
        (HilbertRamification.decompositionGroupToLocalization vK
          (RayClass.adicAbv_isNontrivial v) w sigma))
          (e1.symm (e1 (e0 (i x))))) =
        e1 (e0 (i (sigma.1 x)))
    rw [e1.symm_apply_apply, AlgEquiv.autCongr_apply]
    change
      e1 (e0
        (HilbertRamification.decompositionGroupToLocalization vK
          (RayClass.adicAbv_isNontrivial v) w sigma
          (e0.symm (e0 (i x))))) =
        e1 (e0 (i (sigma.1 x)))
    rw [e0.symm_apply_apply,
      HilbertRamification.decompositionGroupToLocalization_toLocalization]
  · intro x
    change e1 (e0 (i (algebraMap K (AlgebraicClosure K) x))) = _
    rw [AbsoluteValue.toAlgebraicLocalization_algebraMap]
    rw [e0.commutes]
    rw [IsAlgClosure.equivOfEquiv_algebraMap]
    exact congrArg
      (algebraMap (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))) (c.commutes x)

/-- The selected algebraic-localization embedding from a number field's
algebraic closure to an algebraic closure of one concrete adic completion. -/
noncomputable def finitePlaceAlgebraicClosureEmbedding
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AlgebraicClosure K →+* AlgebraicClosure (v.adicCompletion K) :=
  (finitePlaceAlgebraicClosureEmbeddingData K v).embedding

/-- The selected global-to-local algebraic-closure embedding intertwines the
decomposition action with the concrete local absolute-Galois action. -/
theorem finitePlaceAlgebraicClosureEmbedding_action
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : finitePlaceAbsoluteDecompositionGroup K v)
    (x : AlgebraicClosure K) :
    absoluteGaloisGroupContinuousMulEquiv
        (v.adicCompletion K)
        (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)
        (finitePlaceAlgebraicClosureEmbedding K v x) =
      finitePlaceAlgebraicClosureEmbedding K v (sigma.1 x) := by
  exact (finitePlaceAlgebraicClosureEmbeddingData K v).action sigma x

/-- The selected algebraic-closure embedding extends the diagonal embedding
of the number field into its concrete adic completion. -/
theorem finitePlaceAlgebraicClosureEmbedding_algebraMap
    (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    finitePlaceAlgebraicClosureEmbedding K v
        (algebraMap K (AlgebraicClosure K) x) =
      algebraMap (v.adicCompletion K)
        (AlgebraicClosure (v.adicCompletion K))
        (algebraMap K (v.adicCompletion K) x) := by
  exact (finitePlaceAlgebraicClosureEmbeddingData K v).algebraMap x

private theorem rootQuotient_eq_of_same_pow_of_primitiveRoots_forComparison
    {K L : Type} [Field K] [Field L] [Algebra K L]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (a : Kˣ) (u u' : Lˣ)
    (hu : u ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a)
    (hu' : u' ^ (n : ℕ) = Units.map (algebraMap K L).toMonoidHom a)
    (sigma : Gal(L / K)) :
    rootQuotient (K := K) (L := L) u sigma =
      rootQuotient (K := K) (L := L) u' sigma := by
  let D := chosenFiniteKummerRadicalDatum (K := K) (L := L) n
  let delta : D.carrier := ⟨a, u, hu⟩
  let hfixed :=
    nthRootsOfUnity_fixed (K := K) (L := L) n
      (nthRootsOfUnityInBase_of_primitiveRoots
        (K := K) (L := L) n hmu)
  calc
    rootQuotient (K := K) (L := L) u sigma =
        D.rootCharacter delta hfixed sigma :=
      D.rootCharacter_eq_of_same_pow hfixed delta hu sigma
    _ = rootQuotient (K := K) (L := L) u' sigma :=
      (D.rootCharacter_eq_of_same_pow hfixed delta hu' sigma).symm

/-- Roots of unity transported through the selected global-to-adic
algebraic-closure embedding. -/
noncomputable def finitePlaceAbsoluteMuPToAdicAddHom
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AbsoluteMuP K p →+ AbsoluteMuP (v.adicCompletion K) p where
  toFun := fun x ↦ Additive.ofMul
    ⟨Units.map (finitePlaceAlgebraicClosureEmbedding K v).toMonoidHom x.toMul,
      by
        change
          Units.map (finitePlaceAlgebraicClosureEmbedding K v).toMonoidHom
              x.toMul ^ p = 1
        rw [← map_pow]
        rw [(mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp x.toMul.property]
        exact map_one _⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact map_one _
  map_add' := by
    intro x y
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    exact map_mul _ _ _

/-- The preceding root-of-unity transport as a `ZMod p`-linear map. -/
noncomputable def finitePlaceAbsoluteMuPToAdic
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    AbsoluteMuP K p →ₗ[ZMod p] AbsoluteMuP (v.adicCompletion K) p :=
  (finitePlaceAbsoluteMuPToAdicAddHom K p v).toZModLinearMap p

/-- Root-of-unity transport intertwines the decomposition action with the
absolute-Galois action of the concrete adic completion. -/
theorem finitePlaceAbsoluteMuPToAdic_action
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (sigma : finitePlaceAbsoluteDecompositionGroup K v)
    (x : AbsoluteMuP K p) :
    finitePlaceAbsoluteMuPToAdic K p v
        (absoluteMuPActionContinuousLinearMap K p sigma.1 x) =
      absoluteMuPActionContinuousLinearMap (v.adicCompletion K) p
        (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)
        (finitePlaceAbsoluteMuPToAdic K p v x) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  simp only [finitePlaceAbsoluteMuPToAdic,
    AddMonoidHom.coe_toZModLinearMap,
    finitePlaceAbsoluteMuPToAdicAddHom,
    absoluteMuPActionContinuousLinearMap_apply,
    absoluteMuPActionAddHom_apply_coe]
  change
    finitePlaceAlgebraicClosureEmbedding K v (sigma.1 x.toMul.1) =
      absoluteGaloisGroupContinuousMulEquiv (v.adicCompletion K)
        (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)
        (finitePlaceAlgebraicClosureEmbedding K v x.toMul.1)
  exact (finitePlaceAlgebraicClosureEmbedding_action K v sigma x.toMul.1).symm

/-- The actual algebraic-localization coefficient transport, followed by the
chosen local `mu_p ≃ ZMod p` coordinate. -/
noncomputable def finitePlaceAbsoluteMuPAdicCoordinate
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty) :
    AbsoluteMuP K p →ₗ[ZMod p] ZMod p :=
  (absoluteMuPLinearEquivZMod (v.adicCompletion K) p hmu).toLinearMap.comp
    (finitePlaceAbsoluteMuPToAdic K p v)

/-- Coefficient transport as a continuous linear map. -/
noncomputable def finitePlaceAbsoluteMuPAdicCoordinateContinuous
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty) :
    AbsoluteMuP K p →L[ZMod p] ZMod p :=
  { toLinearMap := finitePlaceAbsoluteMuPAdicCoordinate K p v hmu
    cont := continuous_of_discreteTopology }

/-- The actual local coefficient coordinate is an intertwining map from the
natural decomposition representation to the trivial `ZMod p` line. -/
noncomputable def finitePlaceAbsoluteMuPAdicCoordinateHom
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty) :
    TopRep.res
        (ContinuousMonoidHom.id (finitePlaceAbsoluteDecompositionGroup K v) :
          finitePlaceAbsoluteDecompositionGroup K v →*
            finitePlaceAbsoluteDecompositionGroup K v)
        (finitePlaceAbsoluteMuPTopRep K p v) ⟶
      trivialZModP p (finitePlaceAbsoluteDecompositionGroup K v) := by
  apply TopRep.ofHom
  exact
    { toContinuousLinearMap :=
        finitePlaceAbsoluteMuPAdicCoordinateContinuous K p v hmu
      isIntertwining' := by
        intro sigma
        apply ContinuousLinearMap.ext
        intro x
        change finitePlaceAbsoluteMuPAdicCoordinate K p v hmu
            (absoluteMuPActionContinuousLinearMap K p sigma.1 x) =
          finitePlaceAbsoluteMuPAdicCoordinate K p v hmu x
        rw [finitePlaceAbsoluteMuPAdicCoordinate, LinearMap.comp_apply]
        rw [finitePlaceAbsoluteMuPToAdic_action K p v sigma x]
        rw [absoluteMuPAction_eq_self_of_primitiveRoots
          (v.adicCompletion K) p hmu]
        rfl }

/-- Degree-one natural-coefficient classes on the decomposition group,
expressed in the local `ZMod p` coordinate. -/
noncomputable def finitePlaceAbsoluteMuPH1AdicCoordinate
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty) :
    continuousCohomology 1 (finitePlaceAbsoluteMuPTopRep K p v) →ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup K v) :=
  ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm.toLinearMap.comp
    (ContinuousCohomology.map
      (ContinuousMonoidHom.id (finitePlaceAbsoluteDecompositionGroup K v))
      (finitePlaceAbsoluteMuPAdicCoordinateHom K p v hmu) 1).hom.toLinearMap

/-- Pull intrinsic local continuous `H¹` back to the selected decomposition
group through the concrete decomposition--adic Galois map. -/
noncomputable def finitePlaceAdicH1Restriction
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    ContinuousH1ZMod
        (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion K)) →ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup K v) := by
  let f : ContinuousH1ZMod
        (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion K)) →+
      ContinuousH1ZMod
        (p := p) (G := finitePlaceAbsoluteDecompositionGroup K v) :=
    { toFun := fun chi ↦ h1OfCharacter
        ((characterOfH1 chi).comp
          (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v))
      map_zero' := by
        ext sigma
        rfl
      map_add' := by
        intro chi psi
        ext sigma
        rfl }
  exact f.toZModLinearMap p

@[simp]
theorem finitePlaceAdicH1Restriction_apply
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (chi : ContinuousH1ZMod
      (p := p) (G := Field.absoluteGaloisGroup (v.adicCompletion K)))
    (sigma : finitePlaceAbsoluteDecompositionGroup K v) :
    finitePlaceAdicH1Restriction K p v chi (Additive.ofMul sigma) =
      chi (Additive.ofMul
        (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)) :=
  rfl

/-- On Kummer root cocycles, the actual local coefficient coordinate agrees
with the intrinsic root cocycle of the localized unit. -/
theorem finitePlaceAbsoluteMuPAdicCoordinate_rootCocycle
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty)
    (a : Kˣ) (sigma : finitePlaceAbsoluteDecompositionGroup K v) :
    finitePlaceAbsoluteMuPAdicCoordinate K p v hmu
        (absoluteKummerMuPRootCocycle K p a sigma.1) =
      absoluteMuPLinearEquivZMod (v.adicCompletion K) p hmu
        (absoluteKummerMuPRootCocycle (v.adicCompletion K) p
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
          (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)) := by
  let C := v.adicCompletion K
  let f := finitePlaceAlgebraicClosureEmbedding K v
  let aC : Cˣ := Units.map (algebraMap K C).toMonoidHom a
  let beta := absoluteKummerChosenRoot K p a
  let betaC : (AlgebraicClosure C)ˣ := Units.map f.toMonoidHom beta
  let tau : Gal(AlgebraicClosure C / C) :=
    absoluteGaloisGroupContinuousMulEquiv C
      (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)
  have hbase :
      Units.map f.toMonoidHom
          (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a) =
        Units.map (algebraMap C (AlgebraicClosure C)).toMonoidHom aC := by
    apply Units.ext
    exact finitePlaceAlgebraicClosureEmbedding_algebraMap K v a.1
  have hbetaCpow :
      betaC ^ p =
        Units.map (algebraMap C (AlgebraicClosure C)).toMonoidHom aC := by
    calc
      betaC ^ p = Units.map f.toMonoidHom (beta ^ p) :=
        (map_pow (Units.map f.toMonoidHom) beta p).symm
      _ = Units.map f.toMonoidHom
          (Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a) := by
        rw [absoluteKummerChosenRoot_pow]
      _ = _ := hbase
  have hmap :
      Units.map f.toMonoidHom
          (rootQuotient (K := K) (L := AlgebraicClosure K) beta sigma.1) =
        rootQuotient (K := C) (L := AlgebraicClosure C) betaC tau := by
    apply Units.ext
    simp only [rootQuotient, Units.coe_map, Units.val_div_eq_div_val]
    change f (sigma.1 beta.1 / beta.1) = tau betaC.1 / betaC.1
    rw [map_div₀]
    exact congrArg (fun z ↦ z / f beta.1)
      (finitePlaceAlgebraicClosureEmbedding_action K v sigma beta.1).symm
  have hchoice :
      rootQuotient (K := C) (L := AlgebraicClosure C) betaC tau =
        rootQuotient (K := C) (L := AlgebraicClosure C)
          (absoluteKummerChosenRoot C p aC) tau :=
    rootQuotient_eq_of_same_pow_of_primitiveRoots_forComparison
      (p.toPNat (Fact.out : p.Prime).pos) hmu aC betaC
        (absoluteKummerChosenRoot C p aC) hbetaCpow
        (absoluteKummerChosenRoot_pow C p aC) tau
  have hcocycle :
      finitePlaceAbsoluteMuPToAdic K p v
          (absoluteKummerMuPRootCocycle K p a sigma.1) =
        absoluteKummerMuPRootCocycle C p aC
          (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change Units.map f.toMonoidHom
        (rootQuotient (K := K) (L := AlgebraicClosure K) beta sigma.1) =
      rootQuotient (K := C) (L := AlgebraicClosure C)
        (absoluteKummerChosenRoot C p aC) tau
    exact hmap.trans hchoice
  rw [finitePlaceAbsoluteMuPAdicCoordinate, LinearMap.comp_apply]
  exact congrArg (absoluteMuPLinearEquivZMod C p hmu) hcocycle

/-- The intrinsic local Kummer class of a global unit, pulled back to the
selected decomposition group. -/
noncomputable def finitePlaceAdicKummerH1OfGlobalUnit
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty)
    (a : Kˣ) :
    ContinuousH1ZMod
      (p := p) (G := finitePlaceAbsoluteDecompositionGroup K v) :=
  finitePlaceAdicH1Restriction K p v
    (absoluteKummerContinuousH1LinearEquiv (v.adicCompletion K) p hmu
      (Additive.ofMul
        (QuotientGroup.mk'
          (powMonoidHom p : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a))))

@[simp]
theorem finitePlaceAdicKummerH1OfGlobalUnit_apply
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty)
    (a : Kˣ) (sigma : finitePlaceAbsoluteDecompositionGroup K v) :
    finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a
        (Additive.ofMul sigma) =
      absoluteMuPLinearEquivZMod (v.adicCompletion K) p hmu
        (absoluteKummerMuPRootCocycle (v.adicCompletion K) p
          (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
          (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)) := by
  rw [finitePlaceAdicKummerH1OfGlobalUnit,
    finitePlaceAdicH1Restriction_apply]
  exact absoluteKummerContinuousH1LinearEquiv_mk_apply
    (v.adicCompletion K) p hmu
    (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
    (finitePlaceDecompositionToAdicAbsoluteGaloisGroup K v sigma)

/-- Mapping the restricted natural Kummer cocycle through the actual local
coefficient coordinate gives the intrinsic local Kummer cocycle pulled back
to the decomposition group. -/
theorem finitePlaceAbsoluteMuPCocyclesMap_kummer_eq_adic
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty)
    (a : Kˣ) :
    ContinuousCohomology.cocyclesMap
        (ContinuousMonoidHom.id (finitePlaceAbsoluteDecompositionGroup K v))
        (finitePlaceAbsoluteMuPAdicCoordinateHom K p v hmu) 1
        (finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle K p v a) =
      ClassFieldTower.Cohomology.cocycleOfH1
        (finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a) := by
  let Czero := ClassFieldTower.Cohomology.trivialZModPCochains p
    (finitePlaceAbsoluteDecompositionGroup K v)
  apply ClassFieldTower.Cohomology.topModule_mono_injective (Czero.iCycles 1)
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
  calc
    _ = ClassFieldTower.Cohomology.homogeneousOneCochainOfH1
        (finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a) := by
      have hrestrict :
          ((TopRep.homogeneousCochains
              (finitePlaceAbsoluteMuPTopRep K p v)).iCycles 1).hom
              (finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle K p v a) =
            (((ContinuousCohomology.cochainsMap
                (finitePlaceAbsoluteDecompositionInclusion K v)
                (finitePlaceAbsoluteMuPRestrictionHom K p v)).f 1).hom
              (((TopRep.homogeneousCochains
                  (absoluteMuPTopRep K p)).iCycles 1).hom
                (absoluteKummerMuPHomogeneousOneCocycle K p a))) := by
        exact ConcreteCategory.congr_hom
          (HomologicalComplex.cyclesMap_i
            (ContinuousCohomology.cochainsMap
              (finitePlaceAbsoluteDecompositionInclusion K v)
              (finitePlaceAbsoluteMuPRestrictionHom K p v)) 1)
          (absoluteKummerMuPHomogeneousOneCocycle K p a)
      rw [ConcreteCategory.comp_apply]
      rw [hrestrict]
      rw [iCycles_absoluteKummerMuPHomogeneousOneCocycle]
      apply Subtype.ext
      ext g h
      rw [ClassFieldTower.Cohomology.homogeneousOneCochainOfH1_apply]
      change finitePlaceAbsoluteMuPAdicCoordinate K p v hmu
          ((absoluteKummerMuPHomogeneousOneCochain K p a).1 g.1 h.1) =
        finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a
          (Additive.ofMul (g⁻¹ * h))
      have hc := absoluteKummerMuPHomogeneousOneCochain_eq_action
        (K := K) (p := p) a g.1 h.1
      rw [hc]
      change finitePlaceAbsoluteMuPAdicCoordinate K p v hmu
          (absoluteMuPActionContinuousLinearMap K p g.1
            (absoluteKummerMuPRootCocycle K p a (g⁻¹ * h).1)) =
        finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a
          (Additive.ofMul (g⁻¹ * h))
      rw [finitePlaceAbsoluteMuPAdicCoordinate, LinearMap.comp_apply]
      rw [finitePlaceAbsoluteMuPToAdic_action K p v g
        (absoluteKummerMuPRootCocycle K p a (g⁻¹ * h).1)]
      rw [absoluteMuPAction_eq_self_of_primitiveRoots
        (v.adicCompletion K) p hmu]
      rw [finitePlaceAdicKummerH1OfGlobalUnit_apply]
      exact finitePlaceAbsoluteMuPAdicCoordinate_rootCocycle
        K p v hmu a (g⁻¹ * h)
    _ = Czero.iCycles 1
        (ClassFieldTower.Cohomology.cocycleOfH1
          (finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a)) :=
      (ClassFieldTower.Cohomology.homogeneousOneCochainOfCocycle_cocycleOfH1
        (finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a)).symm

/-- The localized natural Kummer class becomes the intrinsic local Kummer
class after applying the actual algebraic-localization coordinate. -/
theorem finitePlaceAbsoluteMuPH1AdicCoordinate_kummerClass
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty)
    (a : Kˣ) :
    finitePlaceAbsoluteMuPH1AdicCoordinate K p v hmu
        (finitePlaceAbsoluteKummerMuPH1Class K p v a) =
      finitePlaceAdicKummerH1OfGlobalUnit K p v hmu a := by
  change
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm
      (ContinuousCohomology.map
        (ContinuousMonoidHom.id (finitePlaceAbsoluteDecompositionGroup K v))
        (finitePlaceAbsoluteMuPAdicCoordinateHom K p v hmu) 1
        (ContinuousCohomology.π (finitePlaceAbsoluteMuPTopRep K p v) 1
          (finitePlaceAbsoluteKummerMuPHomogeneousOneCocycle K p v a))) = _
  rw [← ConcreteCategory.comp_apply, ContinuousCohomology.π_map,
    ConcreteCategory.comp_apply]
  rw [finitePlaceAbsoluteMuPCocyclesMap_kummer_eq_adic]
  exact
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm_apply_apply _

/-- The comparison on a represented global power class. -/
theorem finitePlaceAbsoluteMuPKummerH1LinearMap_compare_adic_mk
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty)
    (a : Kˣ) :
    finitePlaceAbsoluteMuPH1AdicCoordinate K p v hmu
        (finitePlaceAbsoluteKummerMuPH1LinearMap K p v
          (Additive.ofMul
            (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))) =
      finitePlaceAdicH1Restriction K p v
        (absoluteKummerContinuousH1LinearEquiv (v.adicCompletion K) p hmu
          (finitePlacePowerClassLocalization K p v
            (Additive.ofMul
              (QuotientGroup.mk'
                (powMonoidHom p : Kˣ →* Kˣ).range a)))) := by
  rw [finitePlaceAbsoluteKummerMuPH1LinearMap_mk,
    finitePlacePowerClassLocalization_mk]
  exact finitePlaceAbsoluteMuPH1AdicCoordinate_kummerClass K p v hmu a

/-- Linear-map form of the finite-place natural/intrinsic Kummer comparison
for any number field whose completion contains the required roots of unity. -/
theorem finitePlaceAbsoluteMuPKummerH1LinearMap_compare_adic
    (K : Type) [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hmu : (primitiveRoots p (v.adicCompletion K)).Nonempty) :
    (finitePlaceAbsoluteMuPH1AdicCoordinate K p v hmu).comp
        (finitePlaceAbsoluteKummerMuPH1LinearMap K p v) =
      (finitePlaceAdicH1Restriction K p v).comp
        ((absoluteKummerContinuousH1LinearEquiv
          (v.adicCompletion K) p hmu).toLinearMap.comp
          (finitePlacePowerClassLocalization K p v)) := by
  apply LinearMap.ext
  intro x
  let q : Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range := Additive.toMul x
  change
    finitePlaceAbsoluteMuPH1AdicCoordinate K p v hmu
        (finitePlaceAbsoluteKummerMuPH1LinearMap K p v (Additive.ofMul q)) =
      finitePlaceAdicH1Restriction K p v
        (absoluteKummerContinuousH1LinearEquiv (v.adicCompletion K) p hmu
          (finitePlacePowerClassLocalization K p v (Additive.ofMul q)))
  refine QuotientGroup.induction_on q ?_
  intro a
  exact finitePlaceAbsoluteMuPKummerH1LinearMap_compare_adic_mk K p v hmu a

/-- Over the cyclotomic base, the natural finite-place Kummer map and the
existing intrinsic completion Kummer equivalence agree after transport to the
common decomposition-group `H¹` coordinate. -/
theorem finitePlaceCyclotomicMuPKummerH1LinearMap_compare
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    (finitePlaceAbsoluteMuPH1AdicCoordinate
      (FinitePlaceCyclotomicBase F p) p v
      (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F p v)).comp
        (finitePlaceAbsoluteKummerMuPH1LinearMap
          (FinitePlaceCyclotomicBase F p) p v) =
      (finitePlaceAdicH1Restriction
        (FinitePlaceCyclotomicBase F p) p v).comp
        ((finitePlaceCyclotomicCompletionKummerH1LinearEquiv
          F p v).toLinearMap.comp
          (finitePlacePowerClassLocalization
            (FinitePlaceCyclotomicBase F p) p v)) := by
  have hlocal :
      (finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v).toLinearMap =
        (absoluteKummerContinuousH1LinearEquiv
          (v.adicCompletion (FinitePlaceCyclotomicBase F p)) p
          (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F p v)).toLinearMap := by
    apply LinearMap.ext
    intro x
    ext sigma
    rfl
  rw [hlocal]
  exact finitePlaceAbsoluteMuPKummerH1LinearMap_compare_adic
    (FinitePlaceCyclotomicBase F p) p v
      (finitePlaceCyclotomicCompletion_primitiveRoots_nonempty F p v)

end ClassFieldTower.Martinet.Shafarevich
