/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.Herbrand.Local
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.Herbrand
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.ArchimedeanNormQuotient
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Galois orbits of logarithmic places above a support
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


/-- The permutation-representation presentation of the action on
logarithmic places above a base support.  This is the presentation used
by the `S`-unit Herbrand theorem. -/
@[reducible]
noncomputable def aboveSLogPlaceMulAction
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MulAction (L ≃ₐ[K] L)
      (SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :=
  permutationMulAction
    (logPlacePermutationHom K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S))

/-- Send a logarithmic place of `L` lying over the pulled-back support
to its underlying unrestricted place of `K`. -/
noncomputable def logPlaceBelowRelativeUnrestrictedIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →
      RelativeUnrestrictedSPlaceIndex (K := K) S
  | Sum.inl W =>
      Sum.inl (W.comap (algebraMap K L))
  | Sum.inr W =>
      Sum.inr
        ⟨finitePlaceBelow (K := K) W.1,
          (mem_finitePlacesAbove_iff
            (K := K) (L := L) S W.1).1 W.2⟩

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The place-below map is constant on Galois orbits of logarithmic
places. -/
theorem logPlaceBelowRelativeUnrestrictedIndex_smul
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (σ : L ≃ₐ[K] L)
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    let :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S (σ • q) =
      logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S q := by
  intro logAction
  cases q with
  | inl W =>
      change
        logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S
            (logPlacePermutationHom K L
              (finitePlacesAbove (K := K) (L := L) S)
              (finitePlacesAbove_isGaloisStable
                (K := K) (L := L) S) σ (Sum.inl W)) =
          logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S (Sum.inl W)
      rw [logPlacePermutationHom_apply]
      change
        Sum.inl ((σ • W).comap (algebraMap K L)) =
          Sum.inl (W.comap (algebraMap K L))
      congr 1
      rw [NumberField.InfinitePlace.comap_smul]
      congr 1
      ext x
      exact σ.symm.commutes x
  | inr W =>
      change
        logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S
            (logPlacePermutationHom K L
              (finitePlacesAbove (K := K) (L := L) S)
              (finitePlacesAbove_isGaloisStable
                (K := K) (L := L) S) σ (Sum.inr W)) =
          logPlaceBelowRelativeUnrestrictedIndex
            (K := K) (L := L) S (Sum.inr W)
      rw [logPlacePermutationHom_apply]
      change
        Sum.inr
            (⟨finitePlaceBelow (K := K)
                (finitePlaceEquiv K L σ W.1), _⟩ :
              {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) =
          Sum.inr
            (⟨finitePlaceBelow (K := K) W.1, _⟩ :
              {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
      congr 1
      apply Subtype.ext
      exact
        finitePlaceBelow_finitePlaceEquiv
          (K := K) (L := L) σ W.1

/-- The map on Galois orbits induced by taking the place below. -/
noncomputable def logPlaceOrbitBelowRelativeUnrestrictedIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    MulAction.orbitRel.Quotient
        (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace
          (K := L)
          (finitePlacesAbove (K := K) (L := L) S)) →
      RelativeUnrestrictedSPlaceIndex (K := K) S := by
  intro logAction
  exact
    Quotient.lift
      (logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S)
      (by
        intro a b hab
        rcases hab with ⟨σ, hσ⟩
        rw [← hσ]
        exact
          logPlaceBelowRelativeUnrestrictedIndex_smul
            (K := K) (L := L) S σ b)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Evaluating the orbit-descended log-place map on a quotient class gives
the original map on any representative. -/
@[simp]
theorem logPlaceOrbitBelowRelativeUnrestrictedIndex_mk
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    logPlaceOrbitBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S (Quotient.mk'' q) =
      logPlaceBelowRelativeUnrestrictedIndex
        (K := K) (L := L) S q :=
  rfl

/-- Galois orbits of logarithmic places of `L` above `S` are
canonically indexed by all infinite places of `K` and the finite
places in `S`. -/
noncomputable def
    logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    letI :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    MulAction.orbitRel.Quotient
        (L ≃ₐ[K] L)
        (SUnitGroup.LogPlace
          (K := L)
          (finitePlacesAbove (K := K) (L := L) S)) ≃
      RelativeUnrestrictedSPlaceIndex (K := K) S := by
  letI stableFiniteAction :=
    stableFinitePlaceMulAction K L
      (finitePlacesAbove (K := K) (L := L) S)
      (finitePlacesAbove_isGaloisStable
        (K := K) (L := L) S)
  letI logAction :=
    aboveSLogPlaceMulAction
      (K := K) (L := L) S
  let f :=
    logPlaceOrbitBelowRelativeUnrestrictedIndex
      (K := K) (L := L) S
  apply Equiv.ofBijective f
  constructor
  · intro x y hxy
    induction x using Quotient.inductionOn' with
    | _ a =>
      induction y using Quotient.inductionOn' with
      | _ b =>
        apply Quotient.sound
        change a ∈ MulAction.orbit (L ≃ₐ[K] L) b
        cases a with
        | inl W₁ =>
            cases b with
            | inl W₂ =>
                have hbelow :
                    W₁.comap (algebraMap K L) =
                      W₂.comap (algebraMap K L) := by
                  exact Sum.inl.inj hxy
                obtain ⟨σ, hσ⟩ :=
                  NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
                    hbelow
                refine ⟨σ⁻¹, ?_⟩
                change
                  logPlacePermutationHom K L
                      (finitePlacesAbove (K := K) (L := L) S)
                      (finitePlacesAbove_isGaloisStable
                        (K := K) (L := L) S) σ⁻¹
                      (Sum.inl W₂) =
                    Sum.inl W₁
                rw [logPlacePermutationHom_apply]
                change Sum.inl (σ⁻¹ • W₂) = Sum.inl W₁
                rw [← hσ, inv_smul_smul]
            | inr W₂ =>
                change
                  Sum.inl (W₁.comap (algebraMap K L)) =
                    Sum.inr
                      (⟨finitePlaceBelow (K := K) W₂.1, _⟩ :
                        {v : HeightOneSpectrum (𝓞 K) // v ∈ S})
                  at hxy
                exact (Sum.inl_ne_inr hxy).elim
        | inr W₁ =>
            cases b with
            | inl W₂ =>
                change
                  Sum.inr
                      (⟨finitePlaceBelow (K := K) W₁.1, _⟩ :
                        {v : HeightOneSpectrum (𝓞 K) // v ∈ S}) =
                    Sum.inl (W₂.comap (algebraMap K L))
                  at hxy
                exact (Sum.inr_ne_inl hxy).elim
            | inr W₂ =>
                have hbelow :
                    finitePlaceBelow (K := K) W₁.1 =
                      finitePlaceBelow (K := K) W₂.1 := by
                  exact congrArg Subtype.val (Sum.inr.inj hxy)
                let v :=
                  finitePlaceBelow (K := K) W₁.1
                let : Finite (L ≃ₐ[K] L) :=
                  IsGaloisGroup.finite (L ≃ₐ[K] L) K L
                let :
                    IsGaloisGroup
                      (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
                  IsGaloisGroup.of_isFractionRing
                    (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
                let : W₁.1.asIdeal.LiesOver v.asIdeal :=
                  ⟨by
                    simp only [v, finitePlaceBelow_asIdeal]⟩
                let : W₂.1.asIdeal.LiesOver v.asIdeal :=
                  ⟨by
                    have h :=
                      congrArg HeightOneSpectrum.asIdeal hbelow
                    simpa only [v, finitePlaceBelow_asIdeal]
                      using h⟩
                obtain ⟨σ, hσ⟩ :=
                  HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
                    v.asIdeal W₁.1.asIdeal W₂.1.asIdeal
                    (L ≃ₐ[K] L)
                have hplace :
                    finitePlaceEquiv K L σ W₁.1 = W₂.1 := by
                  apply HeightOneSpectrum.ext
                  rw [finitePlaceEquiv_asIdeal]
                  exact hσ
                have hsubtype : σ • W₁ = W₂ := by
                  apply Subtype.ext
                  exact hplace
                refine ⟨σ⁻¹, ?_⟩
                change
                  logPlacePermutationHom K L
                      (finitePlacesAbove (K := K) (L := L) S)
                      (finitePlacesAbove_isGaloisStable
                        (K := K) (L := L) S) σ⁻¹
                      (Sum.inr W₂) =
                    Sum.inr W₁
                rw [logPlacePermutationHom_apply]
                change Sum.inr (σ⁻¹ • W₂) = Sum.inr W₁
                rw [← hsubtype, inv_smul_smul]
  · intro i
    cases i with
    | inl v =>
        refine
          ⟨Quotient.mk''
              (Sum.inl
                (chosenInfinitePlaceAbove (L := L) v)), ?_⟩
        exact
          congrArg Sum.inl
            (chosenInfinitePlaceAbove_comap
              (L := L) v)
    | inr v =>
        let w :=
          chosenFinitePlaceExtension (L := L) v.1
        let W :=
          finitePlaceExtensionCentre
            (K := K) (L := L) v.1 w
        have hWbelow :
            finitePlaceBelow (K := K) W = v.1 :=
          finitePlaceBelow_finitePlaceExtensionCentre
            (K := K) (L := L) v.1 w
        have hWmem :
            W ∈ finitePlacesAbove
              (K := K) (L := L) S :=
          (mem_finitePlacesAbove_iff
            (K := K) (L := L) S W).2
            (hWbelow ▸ v.2)
        refine
          ⟨Quotient.mk''
              (Sum.inr
                (⟨W, hWmem⟩ :
                  finitePlacesAbove
                    (K := K) (L := L) S)), ?_⟩
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hWbelow

/-- The local degree attached to a logarithmic place agrees with the
local degree attached to its place below. -/
theorem
    relativeUnrestrictedSPlaceLocalDegree_logPlaceBelow
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (q :
      SUnitGroup.LogPlace
        (K := L)
        (finitePlacesAbove (K := K) (L := L) S)) :
    relativeUnrestrictedSPlaceLocalDegree
        (K := K) (L := L) S
        (logPlaceBelowRelativeUnrestrictedIndex
          (K := K) (L := L) S q) =
      logPlaceLocalDegree K L
        (finitePlacesAbove (K := K) (L := L) S) q := by
  cases q with
  | inl W =>
      classical
      let W₀ :=
        chosenInfinitePlaceAbove
          (L := L) (W.comap (algebraMap K L))
      change
        Nat.card (absoluteValueDecompositionGroup K W₀.1) =
          if NumberField.InfinitePlace.IsUnramified K W
          then 1 else 2
      rw [
        absoluteValueDecompositionGroup_eq_infinitePlaceStabilizer W₀,
        NumberField.InfinitePlace.card_stabilizer]
      have hcomap :
          W₀.comap (algebraMap K L) =
            W.comap (algebraMap K L) :=
        chosenInfinitePlaceAbove_comap
          (L := L) (W.comap (algebraMap K L))
      obtain ⟨τ, hτ⟩ :=
        NumberField.InfinitePlace.exists_smul_eq_of_comap_eq
          hcomap
      rw [← hτ,
        NumberField.InfinitePlace.isUnramified_smul_iff]
  | inr W =>
      let v :=
        finitePlaceBelow (K := K) W.1
      let w :=
        chosenFinitePlaceExtension (L := L) v
      let W₀ :=
        finitePlaceExtensionCentre
          (K := K) (L := L) v w
      let finiteAction := finitePlaceMulAction K L
      let : Finite (L ≃ₐ[K] L) :=
        IsGaloisGroup.finite (L ≃ₐ[K] L) K L
      let :
          IsGaloisGroup
            (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
        IsGaloisGroup.of_isFractionRing
          (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
      let : W₀.asIdeal.LiesOver v.asIdeal :=
        ⟨(finitePlaceExtensionCentreIdeal_under
          (K := K) (L := L) v w).symm⟩
      let : W.1.asIdeal.LiesOver v.asIdeal :=
        ⟨by
          simp only [v, finitePlaceBelow_asIdeal]⟩
      obtain ⟨τ, hτ⟩ :=
        HilbertRamification.Dedekind.exists_smul_eq_of_isGaloisGroup
          v.asIdeal W₀.asIdeal W.1.asIdeal
          (L ≃ₐ[K] L)
      have hplace :
          finitePlaceEquiv K L τ W₀ = W.1 := by
        apply HeightOneSpectrum.ext
        rw [finitePlaceEquiv_asIdeal]
        exact hτ
      have hcard :
          Nat.card
              (MulAction.stabilizer (L ≃ₐ[K] L) W₀) =
            Nat.card
              (MulAction.stabilizer (L ≃ₐ[K] L) W.1) :=
        Nat.card_congr
          (MulAction.stabilizerEquivStabilizer
            hplace.symm).toEquiv
      change
        Nat.card (absoluteValueDecompositionGroup K w.1) =
          finiteLogPlaceLocalDegree K L W.1
      rw [
        absoluteValueDecompositionGroup_eq_finitePlaceStabilizer
          (K := K) (L := L) v w]
      exact
        hcard.trans
          (finitePlace_stabilizer_card_eq_localDegree
            K L W.1)

/-- The local-degree product occurring in the supported-idele
calculation is exactly the orbit-indexed local-degree product occurring
in the `S`-unit calculation. -/
theorem
    relativeUnrestrictedSPlaceLocalDegree_product_eq_logPlaceOrbitProduct
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let :=
      aboveSLogPlaceMulAction
        (K := K) (L := L) S
    let :
        Fintype
          (MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S))) :=
      Fintype.ofFinite _
    (∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ)) =
      ∏ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)),
        (logPlaceLocalDegree K L
          (finitePlacesAbove (K := K) (L := L) S)
          ω.out : ℚ) := by
  intro logAction orbitFintype
  let e :=
    logPlaceOrbitEquivRelativeUnrestrictedSPlaceIndex
      (K := K) (L := L) S
  calc
    (∏ i,
        (relativeUnrestrictedSPlaceLocalDegree
          (K := K) (L := L) S i : ℚ)) =
        ∏ ω,
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S (e ω) : ℚ) :=
      (e.prod_comp
        (fun i =>
          (relativeUnrestrictedSPlaceLocalDegree
            (K := K) (L := L) S i : ℚ))).symm
    _ =
        ∏ ω :
          MulAction.orbitRel.Quotient
            (L ≃ₐ[K] L)
            (SUnitGroup.LogPlace
              (K := L)
              (finitePlacesAbove
                (K := K) (L := L) S)),
          (logPlaceLocalDegree K L
            (finitePlacesAbove (K := K) (L := L) S)
            ω.out : ℚ) := by
      apply Finset.prod_congr rfl
      intro ω hω
      have he :
          e ω =
            logPlaceBelowRelativeUnrestrictedIndex
              (K := K) (L := L) S ω.out := by
        calc
          e ω = e (Quotient.mk'' ω.out) :=
            congrArg e (Quotient.out_eq' ω).symm
          _ =
              logPlaceBelowRelativeUnrestrictedIndex
                (K := K) (L := L) S ω.out := rfl
      rw [he]
      exact_mod_cast
        relativeUnrestrictedSPlaceLocalDegree_logPlaceBelow
          (K := K) (L := L) S ω.out

end Cohomology
end GlobalClassFieldTheory
