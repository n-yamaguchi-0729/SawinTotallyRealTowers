/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormCore
public import Nyll.ClassFieldTheory.Algebra.TensorNormTransport
public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.PlaceEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FiniteIntegralNormPreimage
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormApproximation.InfinitePlaces
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent

/-!
# Absolute and relative norms of ideles

This module exposes the absolute norm on the idele group and assembles
compatible local determinant-norm preimages into a global relative idele.
-/



@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

universe u v

section LocalNormImages


variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

omit [NumberField L] [IsGalois K L] in
/-- Assemble compatible local determinant-norm preimages into an actual
relative idele.  The only restricted-product input is simultaneous
basis-integrality of the finite preimage and its inverse at almost every
finite place. -/
theorem exists_relativeIdele_norm_eq_of_localTensorPreimages
    (a : IdeleGroup K)
    (zInfinite :
      ∀ w : InfinitePlace K,
        (w.Completion ⊗[K] L)ˣ)
    (zFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ)
    (hInfinite :
      ∀ w : InfinitePlace K,
        infiniteTensorDetNorm (K := K) (L := L) w
            (zInfinite w) =
          IdeleGroup.infiniteComponent w a)
    (hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        _root_.localTensorNorm
            (K := K) (L := L) w (zFinite w) =
          IdeleGroup.finiteComponent w a)
    (hIntegral :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (zFinite w)) :
    ∃ z : RelativeIdeleGroup K L,
      RelativeIdeleGroup.norm K L z = a := by
  let d : RelativeLocalIdeleData (K := K) (L := L) :=
    { infinite := zInfinite
      finite := zFinite
      eventually_integral := fun i =>
        hIntegral.mono fun w hw =>
          relativeBasisIntegralAt_repr_mem
            (K := K) (L := L) w _ hw.1 i
      eventually_inverse_integral := fun i =>
        hIntegral.mono fun w hw =>
          relativeBasisIntegralAt_repr_mem
            (K := K) (L := L) w _ hw.2 i }
  refine
    ⟨relativeIdeleOfLocalData (K := K) (L := L) d, ?_⟩
  apply Prod.ext
  · apply ContinuousMulEquiv.piUnits.injective
    funext w
    change
      IdeleGroup.infiniteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeIdeleOfLocalData
              (K := K) (L := L) d)) =
        IdeleGroup.infiniteComponent w a
    rw [RelativeIdeleGroup.infiniteComponent_norm,
      relativeIdeleOfLocalData_infiniteComponent]
    exact hInfinite w
  · apply RestrictedProduct.ext
    intro w
    change
      IdeleGroup.finiteComponent w
          (RelativeIdeleGroup.norm K L
            (relativeIdeleOfLocalData
              (K := K) (L := L) d)) =
        IdeleGroup.finiteComponent w a
    rw [RelativeIdeleGroup.finiteComponent_norm,
      relativeIdeleOfLocalData_finiteComponent]
    exact hFinite w

omit [NumberField L] [IsGalois K L] in
/-- Membership in every local norm image, together with a restricted
choice of finite local preimages, implies membership in the image of the
global relative-idele norm. -/
theorem idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages
    (a : IdeleGroup K)
    (hInfinite :
      ∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w)
    (zFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        (w.adicCompletion K ⊗[K] L)ˣ)
    (hFinite :
      ∀ w : HeightOneSpectrum (𝓞 K),
        _root_.localTensorNorm
            (K := K) (L := L) w (zFinite w) =
          IdeleGroup.finiteComponent w a)
    (hIntegral :
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        RelativeBasisIntegralUnitAt
          (K := K) (L := L) w (zFinite w)) :
    a ∈ (RelativeIdeleGroup.norm K L).range := by
  have hInfinite' :
      ∀ w : InfinitePlace K,
        ∃ z : (w.Completion ⊗[K] L)ˣ,
          infiniteTensorDetNorm (K := K) (L := L) w z =
            IdeleGroup.infiniteComponent w a := by
    intro w
    simpa [infiniteTensorNormSubgroup] using hInfinite w
  choose zInfinite hNorm using hInfinite'
  obtain ⟨z, hz⟩ :=
    exists_relativeIdele_norm_eq_of_localTensorPreimages
      (K := K) (L := L) a zInfinite zFinite hNorm hFinite hIntegral
  exact ⟨z, hz⟩

omit [NumberField L] [IsGalois K L] in
/-- Every global relative-idele norm belongs to each finite local
determinant-norm image. -/
theorem finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
    (a : IdeleGroup K)
    (ha : a ∈ (RelativeIdeleGroup.norm K L).range)
    (w : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup.finiteComponent w a ∈
      (_root_.localTensorNorm
        (K := K) (L := L) w).range := by
  obtain ⟨z, rfl⟩ := ha
  exact
    ⟨RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z,
      (RelativeIdeleGroup.finiteComponent_norm
        (K := K) (L := L) w z).symm⟩

omit [NumberField L] [IsGalois K L] in
/-- Every global relative-idele norm belongs to each infinite local
determinant-norm image. -/
theorem infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
    (a : IdeleGroup K)
    (ha : a ∈ (RelativeIdeleGroup.norm K L).range)
    (w : InfinitePlace K) :
    IdeleGroup.infiniteComponent w a ∈
      infiniteTensorNormSubgroup
        (K := K) (L := L) w := by
  obtain ⟨z, rfl⟩ := ha
  exact
    ⟨RelativeIdeleGroup.infiniteComponent
        (K := K) (L := L) w z,
      (RelativeIdeleGroup.infiniteComponent_norm
        (K := K) (L := L) w z).symm⟩

end LocalNormImages

section Native

variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- **Local-to-global norm criterion for ideles.**  An idele is an
actual global relative-idele norm if and only if all of its finite and
infinite components belong to the corresponding determinant-norm
images.  The restrictedness of the global preimage is automatic: at the
cofinitely many places where the given idele is a local integer unit, the
finite local preimage is chosen valuation-integral and is therefore
basis-integral away from the fixed discriminant support. -/
theorem mem_relativeIdeleNorm_range_iff_localTensorNorms_native
    (a : IdeleGroup K) :
    a ∈ (RelativeIdeleGroup.norm K L).range ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈
          infiniteTensorNormSubgroup
            (K := K) (L := L) w) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w a ∈
          (_root_.localTensorNorm
            (K := K) (L := L) w).range) := by
  constructor
  · intro ha
    exact
      ⟨fun w =>
          infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
            (K := K) (L := L) a ha w,
        fun w =>
          finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
            (K := K) (L := L) a ha w⟩
  · rintro ⟨hInfinite, hFinite⟩
    have hChoice :
        ∀ w : HeightOneSpectrum (𝓞 K),
          ∃ z : (w.adicCompletion K ⊗[K] L)ˣ,
            _root_.localTensorNorm
                (K := K) (L := L) w z =
              IdeleGroup.finiteComponent w a ∧
            (IdeleGroup.finiteComponent w a ∈
                (w.adicCompletionIntegers K).units →
              RelativeLocalTensorDecompositionIntegralUnitAt
                (K := K) (L := L) w z) := by
      intro w
      by_cases hwUnit :
          IdeleGroup.finiteComponent w a ∈
            (w.adicCompletionIntegers K).units
      · obtain ⟨z, hz, hzIntegral⟩ :=
          exists_localTensorDecompositionIntegralUnit_localTensorNorm_eq
            (K := K) (L := L) w
            (IdeleGroup.finiteComponent w a)
            (hFinite w) hwUnit
        exact ⟨z, hz, fun _ => hzIntegral⟩
      · obtain ⟨z, hz⟩ := hFinite w
        exact ⟨z, hz, fun h => (hwUnit h).elim⟩
    choose zFinite hFiniteNorm hFiniteIntegral using hChoice
    have hEventuallyUnit :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          IdeleGroup.finiteComponent w a ∈
            (w.adicCompletionIntegers K).units := by
      simpa [IdeleGroup.finiteComponent_apply] using
        FiniteIdeleGroup.eventually_mem_localUnits a.2
    have hIntegral :
        ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
          RelativeBasisIntegralUnitAt
            (K := K) (L := L) w (zFinite w) := by
      filter_upwards [
        hEventuallyUnit,
        (integralTensorComparisonBadPlaces
          (K := K) (L := L)).eventually_cofinite_notMem] with
          w hwUnit hwBad
      exact
        localTensorDecompositionIntegralUnit_imp_relativeBasisIntegralUnitAt_of_notMem
          (K := K) (L := L) w hwBad
          (hFiniteIntegral w hwUnit)
    exact
      idele_mem_relativeNorm_range_of_localNorms_with_integralPreimages
        (K := K) (L := L) a hInfinite zFinite hFiniteNorm hIntegral

end Native

/-- The actual local-to-global idele norm criterion in independent field
universes. The restricted preimage is transported from the same compatible
small model through the original relative-idele norm square. -/
theorem mem_relativeIdeleNorm_range_iff_localTensorNorms
    {K : Type u} {L : Type v}
    [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (a : IdeleGroup K) :
    a ∈ (RelativeIdeleGroup.norm K L).range ↔
      (∀ w : InfinitePlace K,
        IdeleGroup.infiniteComponent w a ∈ infiniteTensorNormSubgroup (K := K) (L := L) w) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        IdeleGroup.finiteComponent w a ∈ (localTensorNorm (K := K) (L := L) w).range) := by
  constructor
  · intro ha
    exact ⟨fun w => infiniteComponent_mem_infiniteTensorNormSubgroup_of_mem_relativeNorm_range
        (K := K) (L := L) a ha w,
      fun w => finiteComponent_mem_localTensorNorm_range_of_mem_relativeNorm_range
        (K := K) (L := L) a ha w⟩
  · rintro ⟨hInfinite, hFinite⟩
    let : Small.{0} K := ClassFieldTheory.numberField_small K
    let : Small.{0} L := ClassFieldTheory.numberField_small L
    let : NumberField (Shrink.{0} K) := ClassFieldTheory.numberField_shrink K
    let : NumberField (Shrink.{0} L) := ClassFieldTheory.numberField_shrink L
    let : Algebra (Shrink.{0} K) (Shrink.{0} L) := HasseArf.shrinkAlgebra K L
    let : FiniteDimensional (Shrink.{0} K) (Shrink.{0} L) :=
      HasseArf.shrink_finiteDimensional K L
    let : IsGalois (Shrink.{0} K) (Shrink.{0} L) :=
      IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv K).symm)
        (g := (Shrink.ringEquiv L).symm) (HasseArf.shrinkAlgebra_commutes K L)
    let eK : K ≃ₐ[ℚ] Shrink.{0} K := (Shrink.ringEquiv K).symm.toRatAlgEquiv
    let eL : L ≃ₐ[ℚ] Shrink.{0} L := (Shrink.ringEquiv L).symm.toRatAlgEquiv
    have hcomm (x : K) : eL (algebraMap K L x) =
        algebraMap (Shrink.{0} K) (Shrink.{0} L) (eK x) :=
      (DFunLike.congr_fun (HasseArf.shrinkAlgebra_commutes K L) x).symm
    let a₀ := ideleCongr eK a
    have hi : ∀ W : InfinitePlace (Shrink.{0} K),
        IdeleGroup.infiniteComponent W a₀ ∈
          infiniteTensorNormSubgroup (K := Shrink.{0} K) (L := Shrink.{0} L) W := by
      intro W
      let w := (ClassFieldTheory.infinitePlaceEquivOfRingEquiv eK.toRingEquiv).symm W
      let eA := infinitePlaceCompletionCongrEquiv eK W
      have hA (x : K) : eA (algebraMap K w.Completion x) =
          algebraMap (Shrink.{0} K) W.Completion (eK x) :=
        infinitePlaceCompletionCongrHom_algebraMap eK W x
      have hnorm := (ClassFieldTheory.tensorNorm_mem_range_iff_of_compatibleEquiv
        eK.toRingEquiv eA eL.toRingEquiv hA hcomm (IdeleGroup.infiniteComponent w a)).mp
          (hInfinite w)
      have hc : IdeleGroup.infiniteComponent W a₀ =
          Units.mapEquiv eA.toMulEquiv (IdeleGroup.infiniteComponent w a) := by
        apply Units.ext
        exact adeleCongr_infiniteComponent eK
          (((IdeleGroup.equivAdeleRingUnits (K := K) a :
            (NumberField.AdeleRing (𝓞 K) K)ˣ) : NumberField.AdeleRing (𝓞 K) K)) W
      rw [hc]
      exact hnorm
    have hf : ∀ W : HeightOneSpectrum (𝓞 (Shrink.{0} K)),
        IdeleGroup.finiteComponent W a₀ ∈
          (localTensorNorm (K := Shrink.{0} K) (L := Shrink.{0} L) W).range := by
      intro W
      let w := (finitePlaceCongr eK).symm W
      let eA := finitePlaceAdicCompletionCongrEquiv eK W
      let : Algebra K (Shrink.{0} K) := eK.toRingHom.toAlgebra
      have hKW : finitePlaceBelow (K := K) W = w := by
        apply HeightOneSpectrum.ext
        rfl
      have hA (x : K) : eA (algebraMap K (w.adicCompletion K) x) =
          algebraMap (Shrink.{0} K) (W.adicCompletion (Shrink.{0} K)) (eK x) := by
        change finitePlaceAdicCompletionMap K (Shrink.{0} K) w ⟨W, hKW⟩
          (x : w.adicCompletion K) = _
        rw [finitePlaceAdicCompletionMap_coe]
        rfl
      have hnorm := (ClassFieldTheory.tensorNorm_mem_range_iff_of_compatibleEquiv
        eK.toRingEquiv eA eL.toRingEquiv hA hcomm (IdeleGroup.finiteComponent w a)).mp
          (hFinite w)
      rw [ideleCongr_finiteComponent]
      exact hnorm
    obtain ⟨z, hz⟩ := (mem_relativeIdeleNorm_range_iff_localTensorNorms_native a₀).mpr ⟨hi, hf⟩
    let E := relativeIdeleCongrOfAlgEquiv eK eL hcomm
    refine ⟨E.symm z, ?_⟩
    apply (ideleCongr eK).injective
    rw [relativeIdeleCongrOfAlgEquiv_norm eK eL hcomm, E.apply_symm_apply]
    exact hz
