/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteRestrictedProductBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.InfinitePlaceAbove
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.InfinitePlaceModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedProduct
public import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion

/-!
# Scalar extension from relative to ordinary ideles

The idele scalar-extension map is induced by the canonical relative adele
ring equivalence. The local tensor formulas describe its infinite and finite
components in the ordinary idele presentation.
-/



@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Reindex the relative completion product by actual infinite
places above `w`. -/
noncomputable def infiniteCompletionProductReindexAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completionˣ) ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.1.Completionˣ := by
  let e :=
    Equiv.piCongrLeft'
      (fun u : AbsoluteValueExtension w.1 L =>
        u.1.Completionˣ)
      (infinitePlaceAboveEquivExtension
        (K := K) (L := L) w).symm
  exact
    { e with
      map_mul' := by
        intro x y
        funext W
        rfl }

/-- Replace the absolute-value completion in every factor by mathlib's
concrete infinite-place completion. -/
noncomputable def infiniteCompletionProductEquivAbove
    (w : InfinitePlace K) :
    (∀ u : AbsoluteValueExtension w.1 L,
      u.1.Completionˣ) ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ :=
  (infiniteCompletionProductReindexAbove
    (K := K) (L := L) w).trans
    (MulEquiv.piCongrRight fun W =>
      Units.mapEquiv
        (RingEquiv.refl W.1.Completion).symm.toMulEquiv)

/-- The canonical local tensor decomposition for the actual archimedean tensor component, with
codomain indexed by concrete infinite places above the base place. -/
noncomputable def infinitePlaceTensorUnitsEquivAbove
    (w : InfinitePlace K) :
    (w.Completion ⊗[K] L)ˣ ≃*
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ := by
  letI : ∀ u : AbsoluteValueExtension w.1 L,
      Algebra w.1.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra w.1 u.1 u.2
  exact
    (infinitePlaceLocalTensorUnitsEquiv
      (K := K) (L := L) w).trans
      ((localTensorUnitsEquivCompletionProduct
        (K := K) (L := L) w.1 w.isNontrivial).trans
        (infiniteCompletionProductEquivAbove
          (K := K) (L := L) w))

/-- Evaluation formula for the archimedean relative-to-ordinary
comparison at a concrete infinite place above the base place. -/
@[simp]
theorem infinitePlaceTensorUnitsEquivAbove_apply
    (w : InfinitePlace K)
    (z : (w.Completion ⊗[K] L)ˣ)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w}) :
    infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L) w z W =
      Units.mapEquiv
          (RingEquiv.refl W.1.Completion).symm.toMulEquiv
        (localTensorUnitsEquivCompletionProduct
          w.1 w.isNontrivial
          (infinitePlaceLocalTensorUnitsEquiv
            (K := K) (L := L) w z)
        (infinitePlaceAboveEquivExtension
          (K := K) (L := L) w W)) :=
  rfl

omit [NumberField K] [NumberField L] [FiniteDimensional K L] in
/-- After replacing the concrete completion by the underlying
absolute-value completion, scalar extension of a local unit is the pure
tensor with right factor one. -/
@[simp]
theorem infinitePlaceLocalTensorUnitsEquiv_infiniteLocalIdeleInclusion_coe
    (w : InfinitePlace K) (x : w.Completionˣ) :
    (infinitePlaceLocalTensorUnitsEquiv
        (K := K) (L := L) w
        (infiniteLocalIdeleInclusion
          (K := K) (L := L) w x) :
      w.1.Completion ⊗[K] L) =
      infinitePlaceCompletionAlgEquiv w
          (x : w.Completion) ⊗ₜ[K] (1 : L) := by
  rfl

/-- On a diagonal extension-field unit, the infinite local
relative-to-ordinary comparison is the ordinary diagonal embedding. -/
theorem infinitePlaceTensorUnitsEquivAbove_localFieldIdeleInclusion
    (w : InfinitePlace K)
    (W : {W : InfinitePlace L //
      infinitePlaceBelow (K := K) W = w})
    (x : Lˣ) :
    infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L) w
        (infiniteLocalFieldIdeleInclusion
          (K := K) (L := L) w x) W =
      Units.map
        (algebraMap L W.1.Completion)
        x := by
  rw [infinitePlaceTensorUnitsEquivAbove_apply]
  apply Units.ext
  simp only [Units.coe_map]
  change completionTensorDecomposition_left w.1 w.isNontrivial
    ((1 : w.1.Completion) ⊗ₜ[K] (x : L))
    (infinitePlaceAboveEquivExtension (K := K) (L := L) w W) =
      algebraMap L W.1.Completion (x : L)
  rw [completionTensorDecomposition_left_tmul_apply]
  simp only [map_one, one_mul]
  exact AbsoluteValue.toCompletion_eq_algebraMap W.1.1 (x : L)

/-- Flatten the products over base infinite places and places above them
to the product over all infinite places of `L`. -/
noncomputable def infinitePlaceAbovePiMulEquiv :
    (∀ w : InfinitePlace K,
      ∀ W : {W : InfinitePlace L //
          infinitePlaceBelow (K := K) W = w},
        W.1.Completionˣ) ≃*
      ∀ W : InfinitePlace L, W.Completionˣ where
  toFun f W :=
    f (infinitePlaceBelow (K := K) W) ⟨W, rfl⟩
  invFun f w W := f W.1
  left_inv f := by
    funext w W
    rcases W with ⟨W, hW⟩
    subst w
    rfl
  right_inv f := by
    funext W
    rfl
  map_mul' f g := by
    funext W
    rfl

/-- The unrestricted product of all archimedean tensor-unit factors is
the product of the concrete archimedean local unit groups of `L`. -/
noncomputable def relativeInfiniteTensorPiMulEquiv :
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ≃*
      ∀ W : InfinitePlace L, W.Completionˣ :=
  (MulEquiv.piCongrRight fun w =>
    infinitePlaceTensorUnitsEquivAbove
      (K := K) (L := L) w).trans
    (infinitePlaceAbovePiMulEquiv
      (K := K) (L := L))

/-- Evaluation of the archimedean tensor-product comparison at an
infinite place of the extension field. -/
@[simp]
theorem relativeInfiniteTensorPiMulEquiv_apply
    (f : ∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ)
    (W : InfinitePlace L) :
    relativeInfiniteTensorPiMulEquiv (K := K) (L := L) f W =
      infinitePlaceTensorUnitsEquivAbove
        (K := K) (L := L)
        (infinitePlaceBelow (K := K) W)
        (f (infinitePlaceBelow (K := K) W))
        ⟨W, rfl⟩ := rfl

/-- The archimedean relative tensor factors form the ordinary infinite
idele group of `L`. -/
noncomputable def relativeInfiniteIdeleMulEquiv :
    (∀ w : InfinitePlace K,
      (w.Completion ⊗[K] L)ˣ) ≃*
      InfiniteIdeleGroup L :=
  (relativeInfiniteTensorPiMulEquiv
    (K := K) (L := L)).trans
    ContinuousMulEquiv.piUnits.symm.toMulEquiv

/-- The finite factor of the standard restricted local product. -/
abbrev RelativeLocalIdeleData.toFiniteData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeFiniteIdeleData (K := K) (L := L) := a.2

omit [NumberField L] in
/-- Projection onto the finite restricted product preserves multiplication. -/
@[simp]
theorem RelativeLocalIdeleData.toFiniteData_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L)) :
    (a * b).toFiniteData = a.toFiniteData * b.toFiniteData := rfl

/-- The local product already has the standard infinite-by-finite decomposition. -/
noncomputable def relativeLocalIdeleDataSplitMulEquiv :
    RelativeLocalIdeleData (K := K) (L := L) ≃*
      ((∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ) ×
        RelativeFiniteIdeleData (K := K) (L := L)) :=
  MulEquiv.refl _

/-- The finite local unit comparison is induced by the corresponding
ring equivalence. -/
theorem finitePlaceTensorUnitsEquivAboveAdic_coe
    (w : HeightOneSpectrum (𝓞 K))
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (W : {W : HeightOneSpectrum (𝓞 L) //
      finitePlaceBelow (K := K) W = w}) :
    ((finitePlaceTensorUnitsEquivAboveAdic
        (K := K) (L := L) w x W :
        (W.1.adicCompletion L)ˣ) :
        W.1.adicCompletion L) =
      finitePlaceTensorRingEquivAboveAdic
        (K := K) (L := L) w
        (x : w.adicCompletion K ⊗[K] L) W := by
  obtain ⟨u, rfl⟩ :=
    (finitePlaceExtensionEquivAbove
      (K := K) (L := L) w).surjective W
  rw [finitePlaceTensorUnitsEquivAboveAdic_apply_extension,
    finitePlaceTensorRingEquivAboveAdic_apply_extension]
  rfl

/-- The flattened finite unit comparison is induced by the flattened
finite ring comparison. -/
theorem relativeFiniteTensorPiMulEquiv_coe
    (x : ∀ w : HeightOneSpectrum (𝓞 K),
      (w.adicCompletion K ⊗[K] L)ˣ)
    (W : HeightOneSpectrum (𝓞 L)) :
    ((relativeFiniteTensorPiMulEquiv
        (K := K) (L := L) x W :
        (W.adicCompletion L)ˣ) :
        W.adicCompletion L) =
      relativeFiniteTensorPiRingEquiv
        (K := K) (L := L)
        (fun w =>
          (x w : w.adicCompletion K ⊗[K] L)) W := by
  rw [relativeFiniteTensorPiMulEquiv_apply,
    relativeFiniteTensorPiRingEquiv_apply]
  exact finitePlaceTensorUnitsEquivAboveAdic_coe
    (K := K) (L := L)
    (finitePlaceBelow (K := K) W)
    (x (finitePlaceBelow (K := K) W)) ⟨W, rfl⟩

/-- Scalar extension on ideles is induced by the canonical adele ring equivalence. -/
noncomputable def relativeIdeleBaseChangeMulEquiv :
    RelativeIdeleGroup K L ≃* IdeleGroup L :=
  Units.mapEquiv (relativeAdeleBaseChangeRingEquiv (K := K) (L := L)).toMulEquiv

/-- The idele comparison is the unit-group map induced by the ring comparison. -/
theorem relativeIdeleBaseChangeMulEquiv_eq_ringUnits
    (z : RelativeIdeleGroup K L) :
    relativeIdeleBaseChangeMulEquiv (K := K) (L := L) z =
      Units.mapEquiv
        (relativeAdeleBaseChangeRingEquiv (K := K) (L := L)).toMulEquiv z :=
  rfl

/-- The infinite component of the relative idele base-change equivalence. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_infinite
    (z : RelativeIdeleGroup K L) :
    IdeleGroup.infinitePart (relativeIdeleBaseChangeMulEquiv (K := K) (L := L) z) =
      relativeInfiniteIdeleMulEquiv (K := K) (L := L)
        (relativeIdeleToLocalData (K := K) (L := L) z).infinite := by
  apply Units.ext
  funext W
  change (relativeIdeleBaseChangeMulEquiv (K := K) (L := L) z).val.1 W = _
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  rfl

/-- The finite component of the relative idele base-change equivalence. -/
@[simp]
theorem relativeIdeleBaseChangeMulEquiv_finite
    (z : RelativeIdeleGroup K L) :
    IdeleGroup.finiteCoordinates (relativeIdeleBaseChangeMulEquiv (K := K) (L := L) z) =
      relativeFiniteIdeleToFiniteIdele (K := K) (L := L)
        (relativeIdeleToLocalData (K := K) (L := L) z).toFiniteData := by
  apply DFunLike.coe_injective
  funext W
  apply Units.ext
  change (relativeIdeleBaseChangeMulEquiv (K := K) (L := L) z).val.2 W = _
  rw [relativeIdeleBaseChangeMulEquiv_eq_ringUnits]
  exact (relativeFiniteTensorPiMulEquiv_coe (K := K) (L := L)
    (fun w => RelativeIdeleGroup.finiteComponent (K := K) (L := L) w z) W).symm
