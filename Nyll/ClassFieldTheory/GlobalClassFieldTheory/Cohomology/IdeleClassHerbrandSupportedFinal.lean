/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandOutsideSupport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.SupportedIdeleExactSequence
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.IdeleClassHerbrandLogPlaceOrbits
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.HerbrandExactSequence

/-!
# The idele-class Herbrand quotient and norm index
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


omit [IsGalois K L] in
/-- Cancellation on the supported short exact sequence: if supported
ideles and `S`-units have quotients `q` and `q / |G|`, respectively,
then the idele-class quotient is `|G|`. -/
theorem
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnitDefined :
      AboveSUnitHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (hSupportedDefined :
      RelativeIdeleSupportedHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (q : ℚ) (hq : q ≠ 0)
    (hSupported :
      letI :=
        relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S)) :=
        hSupportedDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) σ) :=
        hSupportedDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ = q)
    (hUnit :
      letI :=
        sUnitMulDistribMulAction K L
          (finitePlacesAbove (K := K) (L := L) S)
          (finitePlacesAbove_isGaloisStable
            (K := K) (L := L) S)
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
        hUnitDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)) σ) :=
        hUnitDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    letI := ideleClassMulDistribMulAction K L
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
          _ _ _ _ σ hC.1 hC.2 =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  let sUnitAction :=
    sUnitMulDistribMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  let classAction := ideleClassMulDistribMulAction K L
  let hU0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S))) :=
    hUnitDefined.1
  let hUm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ) :=
    hUnitDefined.2
  let hS0 :
      Finite
        (HerbrandH0 (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)) :=
    hSupportedDefined.1
  let hSm :
      Finite
        (HerbrandHMinusOne (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ) :=
    hSupportedDefined.2
  let i :
      SUnitGroup (K := L)
          (finitePlacesAbove (K := K) (L := L) S) →*
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S :=
    sUnitToRelativeIdeleSupported
      (K := K) (L := L) S
  let j :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S →*
        RelativeIdeleGroup.ClassGroup K L :=
    relativeIdeleSupportedToClass
      (K := K) (L := L) S
  have hi :
      ∀ (τ : L ≃ₐ[K] L)
        (x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)),
        i (τ • x) = τ • i x := by
    simpa [i] using
      (sUnitToRelativeIdeleSupported_equivariant
        (K := K) (L := L) S)
  have hj :
      ∀ (τ : L ≃ₐ[K] L)
        (z :
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S),
        j (τ • z) = τ • j z := by
    simpa [j] using
      (relativeIdeleSupportedToClass_equivariant
        (K := K) (L := L) S)
  have hker :
      ∀ z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S,
        j z = 1 ↔
          ∃ x :
            SUnitGroup (K := L)
              (finitePlacesAbove (K := K) (L := L) S),
            i x = z := by
    simpa [i, j] using
      (sUnit_supportedIdele_ideleClass_exact
        (K := K) (L := L) S)
  have hinj : Function.Injective i := by
    simpa [i] using
      (sUnitToRelativeIdeleSupported_injective
        (K := K) (L := L) S)
  have hsurj : Function.Surjective j := by
    simpa [j] using
      (relativeIdeleSupportedToClass_surjective
        (K := K) (L := L) S hSP)
  let hC :
      HerbrandQuotientDefined
        (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L) σ :=
    @herbrandQuotientDefined_right_of_left_middle
      (L ≃ₐ[K] L)
      (SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S))
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      i j hi hj hker hinj hsurj
      σ hgen hUnitDefined hSupportedDefined
  let hC0 := hC.1
  let hCm := hC.2
  have hmul :
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ =
        herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := SUnitGroup (K := L)
              (finitePlacesAbove (K := K) (L := L) S)) σ *
          herbrandQuotient
            (G := L ≃ₐ[K] L)
            (A := RelativeIdeleGroup.ClassGroup K L) σ :=
    @herbrandQuotient_multiplicative_of_shortExact
      (L ≃ₐ[K] L)
      (SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S))
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)
      (RelativeIdeleGroup.ClassGroup K L)
      inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance inferInstance
      i j hi hj hker hinj hsurj σ hgen
      inferInstance inferInstance inferInstance
      inferInstance inferInstance inferInstance
  have hcard :
      (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hfactor :
      q / (Fintype.card (L ≃ₐ[K] L) : ℚ) ≠ 0 :=
    div_ne_zero hq hcard
  refine ⟨hC, ?_⟩
  apply mul_left_cancel₀ hfactor
  calc
    (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          @herbrandQuotient
            (L ≃ₐ[K] L)
            (RelativeIdeleGroup.ClassGroup K L)
            _ _ _ _ σ hC.1 hC.2 =
        q := by
      rw [← hUnit, ← hmul, hSupported]
    _ =
        (q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) *
          (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
      rw [div_mul_cancel₀ q hcard]

/-- The norm-index lower bound obtained from the supported short exact
sequence. -/
theorem
    card_le_ideleClassNorm_index_of_sUnit_supported_values
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnitDefined :
      AboveSUnitHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (hSupportedDefined :
      RelativeIdeleSupportedHerbrandQuotientDefined
        (K := K) (L := L) S σ)
    (q : ℚ) (hq : q ≠ 0)
    (hSupported :
      letI :=
        relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
          (K := K) (L := L) S
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S)) :=
        hSupportedDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) σ) :=
        hSupportedDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) σ = q)
    (hUnit :
      letI :=
        sUnitMulDistribMulAction K L
          (finitePlacesAbove (K := K) (L := L) S)
          (finitePlacesAbove_isGaloisStable
            (K := K) (L := L) S)
      letI : Finite
          (HerbrandH0 (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
        hUnitDefined.1
      letI : Finite
          (HerbrandHMinusOne (L ≃ₐ[K] L)
            (SUnitGroup (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)) σ) :=
        hUnitDefined.2
      herbrandQuotient
          (G := L ≃ₐ[K] L)
          (A := SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) σ =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ)) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.classNorm K L).range.index := by
  let classAction := ideleClassMulDistribMulAction K L
  obtain ⟨hC, hCvalue⟩ :=
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
      (K := K) (L := L) S σ hgen hSP
      hUnitDefined hSupportedDefined q hq hSupported hUnit
  let hC0 := hC.1
  let hCm := hC.2
  rw [ideleClassNorm_index_eq_herbrandH0_card K L]
  apply
    le_herbrandH0_card_of_herbrandQuotient_eq_nat
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      σ (Fintype.card (L ≃ₐ[K] L))
  simpa using hCvalue

/-- With all local and `S`-unit calculations substituted, an unramified
sufficiently large support gives an idele-class Herbrand quotient equal
to the order of the Galois group. -/
theorem
    ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    letI := ideleClassMulDistribMulAction K L
    ∃ hC :
        HerbrandQuotientDefined
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L) σ,
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)
          _ _ _ _ σ hC.1 hC.2 =
        (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
  let T :=
    finitePlacesAbove (K := K) (L := L) S
  let hT :
      IsGaloisStableFinitePlaces K L T :=
    finitePlacesAbove_isGaloisStable
      (K := K) (L := L) S
  let ρ :=
    logPlacePermutationHom K L T hT
  let indexAction :
      MulAction (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace (K := L) T) :=
    permutationMulAction ρ
  let sUnitAction :
      MulDistribMulAction (L ≃ₐ[K] L)
        (SUnitGroup (K := L) T) :=
    sUnitMulDistribMulAction K L T hT
  let orbitFintype :
      Fintype
        (MulAction.orbitRel.Quotient
          (L ≃ₐ[K] L)
          (SUnitGroup.LogPlace (K := L) T)) :=
    Fintype.ofFinite _
  let stabilizerFintype :
      ∀ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace (K := L) T),
        Fintype (permutationOrbitStabilizer ω) :=
    fun _ => Fintype.ofFinite _
  obtain ⟨hUnit, hUnitValue⟩ :=
    sUnit_herbrandQuotient_eq_localDegreeProduct_div_card
      (K := K) (L := L) hT σ hgen
  let supportedAction :=
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
      (K := K) (L := L) S
  obtain ⟨hSupported, hSupportedValue⟩ :=
    relativeIdeleSupported_herbrandQuotient_eq_localDegreeProduct
      (K := K) (L := L) S σ hgen hUnram
  let q : ℚ :=
    ∏ i,
      (relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S i : ℚ)
  have hq : q ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact
      Nat.cast_ne_zero.mpr
        (show
          relativeUnrestrictedSPlaceLocalDegree
              (K := K) (L := L) S i ≠ 0 by
          unfold relativeUnrestrictedSPlaceLocalDegree
          exact Nat.card_pos.ne')
  have hProducts :
      q =
        ∏ ω :
            MulAction.orbitRel.Quotient
              (L ≃ₐ[K] L)
              (SUnitGroup.LogPlace (K := L) T),
          (logPlaceLocalDegree K L T ω.out : ℚ) := by
    simpa [q, T, hT, ρ] using
      (relativeUnrestrictedSPlaceLocalDegree_product_eq_logPlaceOrbitProduct
        (K := K) (L := L) S)
  have hUnitValue' :
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (SUnitGroup (K := L) T)
          _ _ _ _ σ hUnit.1 hUnit.2 =
        q / (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
    rw [hProducts]
    simpa only [indexAction, ρ, T, hT] using hUnitValue
  have hSupportedValue' :
      @herbrandQuotient
          (L ≃ₐ[K] L)
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S)
          _ _ _ _ σ hSupported.1 hSupported.2 =
        q := by
    exact hSupportedValue
  exact
    ideleClass_herbrandQuotient_eq_card_of_sUnit_supported_values
      (K := K) (L := L) S σ hgen hSP
      hUnit hSupported q hq
      hSupportedValue' hUnitValue'

/-- The corresponding norm-index lower bound with all supported local
calculations substituted. -/
theorem
    card_le_ideleClassNorm_index_of_supported_local_calculation
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ)
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤)
    (hUnram : ∀ w : HeightOneSpectrum (𝓞 K),
      w ∉ S →
        ChosenFinitePlaceIsUnramified
          (K := K) (L := L) w) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.classNorm K L).range.index := by
  let classAction := ideleClassMulDistribMulAction K L
  obtain ⟨hC, hCvalue⟩ :=
    ideleClass_herbrandQuotient_eq_card_of_supported_local_calculation
      (K := K) (L := L) S σ hgen hSP hUnram
  let hC0 := hC.1
  let hCm := hC.2
  rw [ideleClassNorm_index_eq_herbrandH0_card K L]
  apply
    le_herbrandH0_card_of_herbrandQuotient_eq_nat
      (G := L ≃ₐ[K] L)
      (A := RelativeIdeleGroup.ClassGroup K L)
      σ (Fintype.card (L ≃ₐ[K] L))
  simpa using hCvalue

/-- Unconditional norm-index lower bound for a cyclic extension, in
Galois-group-order form. -/
theorem card_le_ideleClassNorm_index
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    Fintype.card (L ≃ₐ[K] L) ≤
      (RelativeIdeleGroup.classNorm K L).range.index :=
  card_le_ideleClassNorm_index_of_supported_local_calculation
    (K := K) (L := L)
    (ideleClassHerbrandSupport (K := K) (L := L))
    σ hgen
    (relativeSupportedAboveHerbrandSupport_sup_principal_eq_top
      (K := K) (L := L))
    (chosenFinitePlaceIsUnramified_of_notMem_ideleClassHerbrandSupport
      (K := K) (L := L))

/-- Unconditional norm-index lower bound in extension-degree form. -/
theorem finrank_le_ideleClassNorm_index
    (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L,
      τ ∈ Subgroup.zpowers σ) :
    Module.finrank K L ≤
      (RelativeIdeleGroup.classNorm K L).range.index := by
  simpa only [Fintype.card_eq_nat_card,
    IsGalois.card_aut_eq_finrank K L] using
    card_le_ideleClassNorm_index
      (K := K) (L := L) σ hgen

end Cohomology
end GlobalClassFieldTheory
