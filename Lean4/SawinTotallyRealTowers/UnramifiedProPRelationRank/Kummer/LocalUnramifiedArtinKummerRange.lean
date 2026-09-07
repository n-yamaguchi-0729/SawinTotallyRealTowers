import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalKummerInertia
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.Filtered.InertiaUnramifiedExtension
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalUnramifiedKummerValuationDual
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalArtinKummerH1Duality

set_option autoImplicit false
/-!
# Unramified Artin--Kummer duality and the valuation line

The intrinsic inertia-trivial subspace of local continuous `H¹` is sent by
the Artin--Kummer pairing precisely onto the valuation line in the dual.
The proof uses actual unramified Kummer extensions and their Frobenius action,
and applies also when the residue characteristic is the coefficient prime.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory LocalClassFieldTheory

variable (K : Type) [Field K] [CharZero K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localUnramifiedArtinKummerRangeTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance localUnramifiedArtinKummerRangeDiscreteTopology : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance localUnramifiedArtinKummerRangeModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) := continuousH1ZModModule

/-- Intrinsic unramified `H¹`, written in the standard absolute-Galois model. -/
noncomputable def localStandardUnramifiedH1 :
    Submodule (ZMod (n : ℕ))
      (ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :=
  (localIntrinsicUnramifiedH1 K (n : ℕ)).comap
    (localStandardH1LinearEquivSeparable (n : ℕ) K).toLinearMap

/-- An inertia-trivial Kummer character defines an actually unramified
chosen simple extension, including in residue characteristic `n`. -/
theorem isUnramifiedChosenSimpleKummer_of_kummerH1_mem
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (ha : absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu
      (Additive.ofMul
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)) ∈
          localStandardUnramifiedH1 K n) :
    IsUnramifiedChosenSimpleKummer K n
      (Nat.cast_ne_zero.mpr (Fact.out : (n : ℕ).Prime).ne_zero) a := by
  let hnK : ((n : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  let E := chosenSimpleKummerExtension K n hnK a
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K n hnK a
  let : IsAbelianGalois K E :=
    chosenSimpleKummerExtension_isAbelianGalois K n hnK hmu a
  exact localIntermediateField_isUnramified_of_inertia_le K E
    ((localKummerH1_mem_unramified_iff_inertia_le (n : ℕ) K hmu a).1 ha)

/-- The local valuation, transported through absolute Kummer theory. -/
noncomputable def localStandardH1Valuation
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K) →ₗ[ZMod (n : ℕ)] ZMod (n : ℕ) :=
  (localPowerClassValuation K (n : ℕ)).comp
    (absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu).symm.toLinearMap

/-- The valuation line in the dual of standard local `H¹`. -/
noncomputable def localStandardH1ValuationDualEmbedding
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    ZMod (n : ℕ) →ₗ[ZMod (n : ℕ)] Module.Dual (ZMod (n : ℕ))
      (ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :=
  (absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu).symm.toLinearMap.dualMap.comp
    (localPowerClassValuationDualEmbedding K (n : ℕ))

@[simp]
theorem localStandardH1ValuationDualEmbedding_apply
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : ZMod (n : ℕ))
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :
    localStandardH1ValuationDualEmbedding K n hmu a chi =
      a * localStandardH1Valuation K n hmu chi := rfl

/-- The local Artin--Kummer functional of an unramified radical is the
Frobenius-scaled valuation functional on `H¹`. -/
theorem localArtinKummerH1DualEmbedding_mk_unramified
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a : Kˣ)
    (ha : IsUnramifiedChosenSimpleKummer K n
      (Nat.cast_ne_zero.mpr (Fact.out : (n : ℕ).Prime).ne_zero) a) :
    localArtinKummerH1DualEmbedding K n hmu
        (absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu
          (Additive.ofMul
            (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a))) =
      localStandardH1ValuationDualEmbedding K n hmu
        (unramifiedChosenSimpleKummerFrobeniusScalar K n hmu a ha) := by
  apply LinearMap.ext
  intro psi
  let qa : absolutePowerClassModP K (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
  change
    (localArtinKummerH1DualEmbedding K n hmu
      (absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu qa)) psi = _
  rw [localArtinKummerH1DualEmbedding_apply, LinearEquiv.symm_apply_apply]
  exact LinearMap.congr_fun
    (localHilbertDualEmbedding_mk_unramified K n hmu a ha)
    ((absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu).symm psi)

/-- Intrinsic unramified classes map into the valuation dual line under
local Artin--Kummer duality. -/
theorem localArtinKummerH1DualEmbedding_mem_valuation_range
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K))
    (hchi : chi ∈ localStandardUnramifiedH1 K n) :
    localArtinKummerH1DualEmbedding K n hmu chi ∈
      LinearMap.range (localStandardH1ValuationDualEmbedding K n hmu) := by
  let e := absoluteKummerContinuousH1LinearEquiv K (n : ℕ) hmu
  let q : Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range :=
    (show Additive (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) from e.symm chi).toMul
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range q
  have hchiEq : chi = e (Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)) := by
    rw [ha]
    exact (e.apply_symm_apply chi).symm
  have haUn := isUnramifiedChosenSimpleKummer_of_kummerH1_mem K n hmu a
    (hchiEq ▸ hchi)
  refine ⟨unramifiedChosenSimpleKummerFrobeniusScalar K n hmu a haUn, ?_⟩
  rw [hchiEq]
  exact (localArtinKummerH1DualEmbedding_mk_unramified K n hmu a haUn).symm

omit [CharZero K] in
/-- The intrinsic unramified line is not zero. -/
theorem localStandardUnramifiedH1_exists_ne_zero :
    ∃ chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K),
      chi ∈ localStandardUnramifiedH1 K n ∧ chi ≠ 0 := by
  let e := localStandardH1LinearEquivSeparable (n : ℕ) K
  let chi := e.symm (localResidueDegreeModPH1 K (n : ℕ))
  refine ⟨chi, ?_, ?_⟩
  · change e chi ∈ localIntrinsicUnramifiedH1 K (n : ℕ)
    rw [e.apply_symm_apply]
    exact localResidueDegreeModPH1_mem_unramified K (n : ℕ)
  · intro hzero
    have hdegree : localResidueDegreeModPH1 K (n : ℕ) = 0 := by
      have h := congrArg e hzero
      simpa only [chi, e.apply_symm_apply, map_zero] using h
    have hline : localResidueDegreeModPH1Line K (n : ℕ) 1 =
        localResidueDegreeModPH1Line K (n : ℕ) 0 := by
      change (1 : ZMod (n : ℕ)) • localResidueDegreeModPH1 K (n : ℕ) =
        (0 : ZMod (n : ℕ)) • localResidueDegreeModPH1 K (n : ℕ)
      simp only [hdegree, smul_zero]
    exact one_ne_zero (localResidueDegreeModPH1Line_injective K (n : ℕ) hline)

/-- Local Artin--Kummer duality takes intrinsic unramified `H¹` exactly
onto the valuation dual line. -/
theorem localArtinKummerH1DualEmbedding_unramified_range
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    LinearMap.range
        ((localArtinKummerH1DualEmbedding K n hmu).comp
          (localStandardUnramifiedH1 K n).subtype) =
      LinearMap.range (localStandardH1ValuationDualEmbedding K n hmu) := by
  apply le_antisymm
  · rintro phi ⟨chi, rfl⟩
    exact localArtinKummerH1DualEmbedding_mem_valuation_range K n hmu chi.1 chi.property
  · obtain ⟨chi, hchi, hchi0⟩ := localStandardUnramifiedH1_exists_ne_zero K n
    obtain ⟨c, hc⟩ := localArtinKummerH1DualEmbedding_mem_valuation_range K n hmu chi hchi
    have hc0 : c ≠ 0 := by
      intro hzero
      apply hchi0
      apply localArtinKummerH1DualEmbedding_injective K n hmu
      rw [← hc, hzero, map_zero, map_zero]
    rintro phi ⟨b, rfl⟩
    refine ⟨⟨(b / c) • chi, (localStandardUnramifiedH1 K n).smul_mem _ hchi⟩, ?_⟩
    change localArtinKummerH1DualEmbedding K n hmu
      ((b / c) • chi) = localStandardH1ValuationDualEmbedding K n hmu b
    rw [map_smul, ← hc, ← map_smul]
    congr 1
    exact div_mul_cancel₀ b hc0

end ClassFieldTower.Martinet.Shafarevich
