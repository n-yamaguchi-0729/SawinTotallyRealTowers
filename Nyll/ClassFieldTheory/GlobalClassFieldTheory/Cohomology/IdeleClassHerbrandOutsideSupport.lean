/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteLocalFactor

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Factors
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.ChosenPlace
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Reassociation
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.BinaryProduct
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product

/-!
# The unramified factors outside the Herbrand support
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology

open CyclicCohomology.ProfiniteCohomology.Herbrand
open CyclicCohomology
open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]


/-- Outside the canonical Herbrand support, the chosen completed local
extension is unramified. -/
theorem
    chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
    (v : HeightOneSpectrum (𝓞 K))
    (hv :
      v ∉ ideleClassHerbrandSupport (K := K) (L := L)) :
    ChosenFinitePlaceIsUnramified
      (K := K) (L := L) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
    (K := K) (L := L) v
  apply isUnramifiedAt_of_notMem_ideleClassHerbrandSupport
    (K := K) (L := L) v hv
  exact
    finitePlaceBelow_finitePlaceExtensionCentre
      (K := K) (L := L) v
      (chosenFinitePlaceExtension (L := L) v)

omit [NumberField L] in
/-- If every chosen finite extension outside `S` is unramified, both
low-degree Tate cohomology groups of the product of its integral
factors are singletons. -/
theorem
    relativeOutsideSPlaceFactors_unramifiedHerbrand_subsingleton
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI :=
      relativeOutsideSPlaceFactorsAction
        (K := K) (L := L) S
    Subsingleton
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S)) ∧
      Subsingleton
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ) := by
  let componentAction :
      ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
        MulDistribMulAction (L ≃ₐ[K] L)
          (relativeLocalTensorDecompositionIntegralUnitSubgroup
            (K := K) (L := L) w.1) :=
    fun w =>
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w.1
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  let e0 :
      HerbrandH0 (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) ≃*
        ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
          HerbrandH0 (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) :=
    herbrandH0PiEquiv
      (G := L ≃ₐ[K] L)
      (fun w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1)
  let em :
      HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ ≃*
        ∀ w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S},
          HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) σ :=
    herbrandHMinusOnePiEquiv
      (G := L ≃ₐ[K] L)
      (fun w : {w : HeightOneSpectrum (𝓞 K) // w ∉ S} =>
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w.1) σ
  constructor
  · constructor
    intro x y
    apply e0.injective
    funext w
    let :
        Subsingleton
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1)) :=
      relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandH0_subsingleton
        (K := K) (L := L) w.1 σ hgen (hUnram w.1 w.2)
    exact Subsingleton.elim _ _
  · constructor
    intro x y
    apply em.injective
    funext w
    let :
        Subsingleton
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeLocalTensorDecompositionIntegralUnitSubgroup
              (K := K) (L := L) w.1) σ) :=
      relativeLocalTensorDecompositionIntegralUnitSubgroup_unramifiedHerbrandHMinusOne_subsingleton
        (K := K) (L := L) w.1 σ hgen (hUnram w.1 w.2)
    exact Subsingleton.elim _ _

omit [NumberField L] in
/-- The product of integral factors outside an unramified support has
Herbrand quotient one. -/
theorem
    relativeOutsideSPlaceFactors_unramifiedHerbrandQuotient_eq_one
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    let :=
      relativeOutsideSPlaceFactorsAction
        (K := K) (L := L) S
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeOutsideSPlaceFactors
            (K := K) (L := L) S)
          _ _ _ _ σ h.1 h.2 = 1 := by
  intro outsideAction
  have hsub :=
    relativeOutsideSPlaceFactors_unramifiedHerbrand_subsingleton
      (K := K) (L := L) S σ hgen hUnram
  let h0Subsingleton := hsub.1
  let hmSubsingleton := hsub.2
  let h :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ :=
    ⟨Finite.of_subsingleton, Finite.of_subsingleton⟩
  refine ⟨h, ?_⟩
  let h0Finite := h.1
  let hmFinite := h.2
  let : Inhabited
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S)) :=
    ⟨1⟩
  let : Inhabited
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ) :=
    ⟨1⟩
  let : Unique
      (HerbrandH0 (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S)) :=
    Unique.mk' _
  let : Unique
      (HerbrandHMinusOne (L ≃ₐ[K] L)
        (RelativeOutsideSPlaceFactors
          (K := K) (L := L) S) σ) :=
    Unique.mk' _
  rw [herbrandQuotient_eq_card_ratio,
    Nat.card_unique,
    Nat.card_unique]
  norm_num

omit [NumberField L] in
/-- After the unramified outside factors have been removed, the supported
relative ideles have Herbrand quotient equal to the product of the local
degrees at the unrestricted factors. -/
theorem
    relativeIdeleSupported_herbrandQuotient_eq_localDegreeProduct
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    let :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ∃ h :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ h.1 h.2 =
        ∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ) := by
  intro supportedAction
  let unrestrictedAction :=
    relativeUnrestrictedSPlaceFactorsAction
      (K := K) (L := L) S
  let outsideAction :=
    relativeOutsideSPlaceFactorsAction
      (K := K) (L := L) S
  let hU :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeUnrestrictedSPlaceFactors
          (K := K) (L := L) S) σ :=
    ⟨relativeUnrestrictedSPlaceFactorsHerbrandH0Finite
        S σ hgen,
      relativeUnrestrictedSPlaceFactorsHerbrandHMinusOneFinite
        S σ hgen⟩
  obtain ⟨hO, hOq⟩ :=
    relativeOutsideSPlaceFactors_unramifiedHerbrandQuotient_eq_one
      (K := K) (L := L) S σ hgen hUnram
  let hU0 := hU.1
  let hUm := hU.2
  let hO0 := hO.1
  let hOm := hO.2
  let hProd0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S)) :=
    herbrandH0ProdFinite _ _
  let hProdm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ) :=
    herbrandHMinusOneProdFinite _ _ σ
  let e0 :
      HerbrandH0 (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) ≃*
        HerbrandH0 (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) :=
    relativeIdeleSupportedHerbrandH0EquivUnrestrictedProdOutside
      (K := K) (L := L) S
  let em :
      HerbrandHMinusOne (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ ≃*
        HerbrandHMinusOne (L ≃ₐ[K] L)
          (RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S ×
            RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ :=
    relativeIdeleSupportedHerbrandHMinusOneEquivUnrestrictedProdOutside
      (K := K) (L := L) S σ
  let hSupported :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S) σ :=
    ⟨Finite.of_equiv _ e0.symm.toEquiv,
      Finite.of_equiv _ em.symm.toEquiv⟩
  refine ⟨hSupported, ?_⟩
  let hS0 := hSupported.1
  let hSm := hSupported.2
  calc
    @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ hSupported.1 hSupported.2 =
        herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A :=
            RelativeUnrestrictedSPlaceFactors
                (K := K) (L := L) S ×
              RelativeOutsideSPlaceFactors
                (K := K) (L := L) S) σ :=
      herbrandQuotient_eq_of_equivariantMulEquiv
        (relativeIdeleSupportedEquivUnrestrictedProdOutside
          (K := K) (L := L) S)
        (relativeIdeleSupportedEquivUnrestrictedProdOutside_smul
          (K := K) (L := L) S) σ
    _ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeUnrestrictedSPlaceFactors
              (K := K) (L := L) S) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeOutsideSPlaceFactors
              (K := K) (L := L) S) σ :=
      herbrandQuotient_prod _ _ σ
    _ =
        (∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ)) * 1 := by
      rw [
        relativeUnrestrictedSPlaceFactors_herbrandQuotient
          (K := K) (L := L) S σ hgen,
        hOq]
    _ =
        ∏ i,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ) := mul_one _

end Cohomology
end GlobalClassFieldTheory
