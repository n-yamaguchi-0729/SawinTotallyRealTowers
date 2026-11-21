/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteLocalFactor

public import Nyll.GaloisCohomology.ProP.MultiplicativeProductH2
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.SupportedIdeleH2Localization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.UnramifiedFinitePlaceIntegralBlockH2
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.UnramifiedInfinitePlaceBlockH2
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces

/-!
# H² of the everywhere-integral relative idele subgroup

The finite integral and infinite unrestricted tensor blocks have already
been proved to have zero H². Coordinatewise primitives assemble across
their products, and the actual equivariant S-place factor decomposition
identifies the result with the relative idele subgroup integral at every
finite place. No unproved Shapiro or restricted-product glue is assumed.

The supported subgroup and its factors retain the actions of the common
S-place decomposition.
-/

@[expose] public section

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
local notation "S" => (∅ : Finset V)
local notation "A∞" => (fun v : InfinitePlace K ↦ (InfinitePlace.Completion v ⊗[K] L)ˣ)
local notation "Ain" => (fun v : {v : V // v ∈ S} ↦
  (HeightOneSpectrum.adicCompletion K (Subtype.val v) ⊗[K] L)ˣ)
local notation "Aout" => (fun v : {v : V // v ∉ S} ↦
  relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) (Subtype.val v))

attribute [local instance] scalarTensorUnitsAction finitePlaceScalarTensorUnitsAction
  relativeLocalTensorDecompositionIntegralUnitSubgroupAction piMulDistribMulAction

omit [NumberField L] in
/-- All actual S-place factors for empty finite support have zero H² in
an everywhere-unramified extension. -/
theorem everywhereUnramifiedEmptySPlaceFactorsH2_subsingleton
    (hfin : ∀ v : V, ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2) := by
  let _ (v : InfinitePlace K) :
      Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (A∞ v)) 2) :=
    unramifiedInfinitePlaceBlockH2_subsingleton K L v (hinf v)
  let _ (v : {v : V // v ∈ S}) :
      Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Ain v)) 2) :=
    (Finset.notMem_empty v.1 v.2).elim
  let _ (v : {v : V // v ∉ S}) :
      Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K) (Aout v)) 2) :=
    unramifiedFinitePlaceIntegralBlockH2_subsingleton K L v.1 (hfin v.1)
  let _ := piMultiplicativeH2_subsingleton (G := Gal(L / K)) A∞
  let _ := piMultiplicativeH2_subsingleton (G := Gal(L / K)) Ain
  let _ := piMultiplicativeH2_subsingleton (G := Gal(L / K)) Aout
  let _ := prodMultiplicativeH2_subsingleton (G := Gal(L / K)) (∀ v, Ain v) (∀ v, Aout v)
  exact prodMultiplicativeH2_subsingleton (G := Gal(L / K))
    (∀ v, A∞ v) ((∀ v, Ain v) × (∀ v, Aout v))

attribute [local instance] relativeIdeleLocalTensorDecompositionSupportedSubgroupAction

omit [NumberField L] in
/-- The subgroup of actual relative ideles integral at every finite
place has zero H² in an everywhere-unramified extension. -/
theorem everywhereUnramifiedSupportedIdeleH2_subsingleton
    (hfin : ∀ v : V, ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2) := by
  let _ := everywhereUnramifiedEmptySPlaceFactorsH2_subsingleton K L hfin hinf
  let hi := supportedSPlaceCohomologyIso K L S
  exact Function.Injective.subsingleton hi.toLinearEquiv.injective

omit [NumberField L] in
/-- A supported idele two-cocycle has an actual supported idele
one-cochain primitive. -/
theorem everywhereUnramifiedSupportedIdeleTwoCocycle_isCoboundary
    (hfin : ∀ v : V, ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K)
    (f : Gal(L / K) × Gal(L / K) →
      relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)
    (hf : groupCohomology.IsMulCocycle₂ f) : groupCohomology.IsMulCoboundary₂ f := by
  let _ := everywhereUnramifiedSupportedIdeleH2_subsingleton K L hfin hinf
  exact isMulCoboundary₂_of_H2_subsingleton f hf

end ClassFieldTower.Martinet.Shafarevich
