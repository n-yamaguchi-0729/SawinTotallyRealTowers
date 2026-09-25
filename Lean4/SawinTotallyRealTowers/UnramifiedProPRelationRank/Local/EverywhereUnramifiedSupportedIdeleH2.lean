/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.MultiplicativeProductH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.UnramifiedFinitePlaceIntegralBlockH2
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.UnramifiedInfinitePlaceBlockH2
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.SPlaces

set_option autoImplicit false
/-!
# H² of the everywhere-integral relative idele subgroup

The finite integral and infinite unrestricted tensor blocks have already
been proved to have zero H². Coordinatewise primitives assemble across
their products, and the actual equivariant S-place factor decomposition
identifies the result with the relative idele subgroup integral at every
finite place. No unproved Shapiro or restricted-product glue is assumed.

The six component actions below have pairwise distinct coefficient types:
three factor families and their products. The seventh action is the
supported-idele subgroup action. Each canonical action is fixed once,
with no alternative tower or repeated statement/proof setup.
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
local notation "S" => (∅ : Finset V)
local notation "A∞" => (fun v : InfinitePlace K ↦ (InfinitePlace.Completion v ⊗[K] L)ˣ)
local notation "Ain" => (fun v : {v : V // v ∈ S} ↦
  (HeightOneSpectrum.adicCompletion K (Subtype.val v) ⊗[K] L)ˣ)
local notation "Aout" => (fun v : {v : V // v ∉ S} ↦
  relativeLocalTensorDecompositionIntegralUnitSubgroup (K := K) (L := L) (Subtype.val v))

local instance supportedH2InfiniteAction (v : InfinitePlace K) :
    MulDistribMulAction Gal(L / K) (A∞ v) :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.Completion)

local instance supportedH2InfiniteProductAction : MulDistribMulAction Gal(L / K) (∀ v, A∞ v) :=
  piMulDistribMulAction Gal(L / K) A∞

local instance supportedH2InsideAction (v : {v : V // v ∈ S}) :
    MulDistribMulAction Gal(L / K) (Ain v) :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.1.adicCompletion K)

local instance supportedH2InsideProductAction : MulDistribMulAction Gal(L / K) (∀ v, Ain v) :=
  piMulDistribMulAction Gal(L / K) Ain

local instance supportedH2OutsideAction (v : {v : V // v ∉ S}) :
    MulDistribMulAction Gal(L / K) (Aout v) :=
  relativeLocalTensorDecompositionIntegralUnitSubgroupAction (K := K) (L := L) v.1

local instance supportedH2OutsideProductAction : MulDistribMulAction Gal(L / K) (∀ v, Aout v) :=
  piMulDistribMulAction Gal(L / K) Aout

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

local instance supportedH2IdeleAction : MulDistribMulAction Gal(L / K)
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S) :=
  relativeIdeleLocalTensorDecompositionSupportedSubgroupAction (K := K) (L := L) S

/-- The subgroup of actual relative ideles integral at every finite
place has zero H² in an everywhere-unramified extension. -/
theorem everywhereUnramifiedSupportedIdeleH2_subsingleton
    (hfin : ∀ v : V, ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2) := by
  let _ := everywhereUnramifiedEmptySPlaceFactorsH2_subsingleton K L hfin hinf
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
  let hi : groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup (K := K) (L := L) S)) 2 ≅
      groupCohomology (Rep.ofMulDistribMulAction Gal(L / K)
        (RelativeIdeleSPlaceFactors (K := K) (L := L) S)) 2 :=
    (groupCohomology.functor ℤ Gal(L / K) 2).mapIso i
  exact Function.Injective.subsingleton hi.toLinearEquiv.injective

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
