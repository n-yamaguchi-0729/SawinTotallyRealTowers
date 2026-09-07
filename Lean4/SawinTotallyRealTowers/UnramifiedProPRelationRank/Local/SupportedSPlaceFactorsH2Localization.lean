import GaloisCohomology.ProP.MultiplicativeProductH2
import GaloisCohomology.ProP.MultiplicativeProductH2Evaluation
import GaloisCohomology.ProP.MultiplicativeBinaryProductH2Evaluation
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedFinitePlaceIntegralBlockH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.UnramifiedInfinitePlaceBlockH2
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces

set_option autoImplicit false
/-!
# Degree-two localization of supported idele factors

The cohomology class of the S-place factors is determined by its finite
coordinates in S when the outside integral blocks and infinite blocks
are unramified. This detects classes by actual coordinate maps.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology CyclicCohomology
open AlgebraicNumberTheory.Valuations HilbertRamification LocalClassFieldTheory

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

local notation "V" => HeightOneSpectrum (𝓞 K)
variable (S : Finset (HeightOneSpectrum (𝓞 K)))
local notation "A∞" => (fun v : InfinitePlace K ↦ (InfinitePlace.Completion v ⊗[K] L)ˣ)
local notation "Ain" => (fun v : {v : V // v ∈ S} ↦
  (HeightOneSpectrum.adicCompletion K (Subtype.val v) ⊗[K] L)ˣ)
local notation "Aout" => (fun v : {v : V // v ∉ S} ↦
  relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) (Subtype.val v))

local instance localizedH2InfiniteAction (v : InfinitePlace K) :
    MulDistribMulAction Gal(L / K) (A∞ v) :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.Completion)

local instance localizedH2InfiniteProductAction : MulDistribMulAction Gal(L / K) (∀ v, A∞ v) :=
  piMulDistribMulAction Gal(L / K) A∞

local instance localizedH2InsideAction (v : {v : V // v ∈ S}) :
    MulDistribMulAction Gal(L / K) (Ain v) :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.1.adicCompletion K)

local instance localizedH2InsideProductAction : MulDistribMulAction Gal(L / K) (∀ v, Ain v) :=
  piMulDistribMulAction Gal(L / K) Ain

local instance localizedH2OutsideAction (v : {v : V // v ∉ S}) :
    MulDistribMulAction Gal(L / K) (Aout v) :=
  relativeLocalTensorDecompositionIntegralUnitSubgroupAction (K := K) (L := L) v.1

local instance localizedH2OutsideProductAction : MulDistribMulAction Gal(L / K) (∀ v, Aout v) :=
  piMulDistribMulAction Gal(L / K) Aout

/-- Evaluate the actual S-place cohomology class in each unrestricted
finite tensor block belonging to S. -/
noncomputable def sPlaceFactorsH2Localization :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2 →+
      ∀ v : {v : V // v ∈ S},
        groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Ain v)) 2 where
  toFun x := piMultiplicativeH2Evaluation Ain
    (prodMultiplicativeH2Evaluation (∀ v, Ain v) (∀ v, Aout v)
      (prodMultiplicativeH2Evaluation (∀ v, A∞ v)
        ((∀ v, Ain v) × (∀ v, Aout v)) x).2).1
  map_zero' := by
    simp only [map_zero, Prod.fst_zero, Prod.snd_zero]
  map_add' x y := by
    simp only [map_add, Prod.fst_add, Prod.snd_add]

omit [NumberField L] in
/-- Outside unramified integral blocks and unramified infinite blocks
leave only the S-indexed finite coordinates in degree two. -/
theorem sPlaceFactorsH2Localization_injective
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Function.Injective (sPlaceFactorsH2Localization K L S) := by
  let _ (v : InfinitePlace K) :
      Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (A∞ v)) 2) :=
    unramifiedInfinitePlaceBlockH2_subsingleton K L v (hinf v)
  let _ (v : {v : V // v ∉ S}) :
      Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Aout v)) 2) :=
    unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v.1 (hfin v.1 v.2)
  let _ := piMultiplicativeH2_subsingleton (G := Gal(L / K)) A∞
  let _ := piMultiplicativeH2_subsingleton (G := Gal(L / K)) Aout
  intro x y h
  apply prodMultiplicativeH2Evaluation_injective (G := Gal(L / K))
    (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v))
  apply Prod.ext
  · exact Subsingleton.elim _ _
  · apply prodMultiplicativeH2Evaluation_injective (G := Gal(L / K))
      (∀ v, Ain v) (∀ v, Aout v)
    apply Prod.ext
    · apply piMultiplicativeH2Evaluation_injective (G := Gal(L / K)) Ain
      exact h
    · exact Subsingleton.elim _ _

local instance localizedH2IdeleAction : MulDistribMulAction Gal(L / K)
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S

private def supportedSPlaceCohomologyIso :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 ≅
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2 := by
  let e := relativeIdeleSupportedEquivSPlaceFactors (K := K) (L := L) S
  let i : Rep.ofMulDistribMulAction Gal(L / K)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) ≅
      Rep.ofMulDistribMulAction Gal(L / K)
        (RelativeIdeleSPlaceFactors (K := K) (L := L) S) :=
    Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (relativeIdeleSupportedComponents_smul (K := K) (L := L) S g x.toMul)))
  exact (groupCohomology.functor ℤ Gal(L / K) 2).mapIso i

/-- Localize a supported idele degree-two class at all finite places in S. -/
noncomputable def supportedSPlaceH2Localization :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 →+
      ∀ v : {v : V // v ∈ S},
        groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Ain v)) 2 :=
  (sPlaceFactorsH2Localization K L S).comp
    (supportedSPlaceCohomologyIso K L S).toLinearEquiv.toAddEquiv.toAddMonoidHom

/-- The actual supported-idele class is determined by the allowed finite
coordinates when all other local blocks are unramified. -/
theorem supportedSPlaceH2Localization_injective
    (hfin : ∀ v : V, v ∉ S → ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Function.Injective (supportedSPlaceH2Localization K L S) :=
  (sPlaceFactorsH2Localization_injective K L S hfin hinf).comp
    (supportedSPlaceCohomologyIso K L S).toLinearEquiv.injective

end ClassFieldTower.Martinet.Shafarevich
