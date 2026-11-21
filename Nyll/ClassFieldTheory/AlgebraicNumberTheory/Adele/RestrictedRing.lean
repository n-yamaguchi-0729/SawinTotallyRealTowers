/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.JointComponents
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteLocalFactor
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic

/-!
# Reconstruction from restricted local adele data
-/

@[expose] public section

open scoped NumberField TensorProduct RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Finite tensor families restricted with respect to the intrinsic integral subrings. -/
abbrev RelativeFiniteAdeleData :=
  Πʳ w : HeightOneSpectrum (𝓞 K),
    [w.adicCompletion K ⊗[K] L,
      relativeLocalTensorDecompositionIntegralSubring (K := K) (L := L) w]

/-- The standard product of the infinite tensor factors and the finite restricted ring. -/
abbrev RelativeLocalAdeleData :=
  (∀ w : InfinitePlace K, w.Completion ⊗[K] L) ×
    RelativeFiniteAdeleData (K := K) (L := L)

omit [NumberField L] in
/-- Infinite tensor components of a restricted adele family. -/
abbrev RelativeLocalAdeleData.infinite
    (a : RelativeLocalAdeleData (K := K) (L := L)) := a.1

omit [NumberField L] in
/-- Finite tensor components of a restricted adele family. -/
abbrev RelativeLocalAdeleData.finite
    (a : RelativeLocalAdeleData (K := K) (L := L)) :
    ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ⊗[K] L := a.2

omit [NumberField L] in
/-- Intrinsic restrictedness gives integral basis coefficients away from finitely many places. -/
theorem RelativeLocalAdeleData.eventually_integral
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (Algebra.TensorProduct.basis (w.adicCompletion K)
        (relativeExtensionBasis (K := K) (L := L))).repr (a.finite w) i ∈
          w.adicCompletionIntegers K := by
  let : NumberField L := NumberField.of_module_finite K L
  filter_upwards [a.2.property,
    (integralTensorComparisonBadPlaces (K := K) (L := L)).eventually_cofinite_notMem]
      with w hw hbad
  exact relativeBasisIntegralAt_repr_mem w (a.finite w)
    ((relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).2 hw) i

omit [NumberField L] in
/-- Assemble an intrinsically restricted family from eventual basis integrality.
The finite exceptional set is used only in this comparison. -/
noncomputable def RelativeLocalAdeleData.ofBasisData
    (infinite : ∀ w : InfinitePlace K, w.Completion ⊗[K] L)
    (finite : ∀ w : HeightOneSpectrum (𝓞 K), w.adicCompletion K ⊗[K] L)
    (hintegral : ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis (w.adicCompletion K)
          (relativeExtensionBasis (K := K) (L := L))).repr (finite w) i ∈
            w.adicCompletionIntegers K) :
    RelativeLocalAdeleData (K := K) (L := L) :=
  ⟨infinite, ⟨finite, by
    let : NumberField L := NumberField.of_module_finite K L
    have hall := Filter.eventually_all.mpr hintegral
    filter_upwards [hall,
      (integralTensorComparisonBadPlaces (K := K) (L := L)).eventually_cofinite_notMem]
        with w hw hbad
    exact (relativeBasisIntegralAt_iff_localTensorDecompositionIntegral_of_notMem
      (K := K) (L := L) w hbad).1
        ((relativeBasisIntegralAt_iff_repr_mem w (finite w)).2 hw)⟩⟩

omit [NumberField L] in
/-- Restricted adele families are determined by their component values. -/
@[ext]
theorem RelativeLocalAdeleData.ext
    {a b : RelativeLocalAdeleData (K := K) (L := L)}
    (hinfinite : a.infinite = b.infinite)
    (hfinite : a.finite = b.finite) :
    a = b :=
  Prod.ext hinfinite (Subtype.ext hfinite)

/-- The `i`-th base-adele coefficient assembled from local tensor
coordinates. -/
noncomputable def relativeLocalAdeleCoefficient
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    NumberField.AdeleRing (𝓞 K) K :=
  ⟨fun w =>
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i,
    ⟨fun w =>
        (Algebra.TensorProduct.basis
            (w.adicCompletion K)
            (relativeExtensionBasis
              (K := K) (L := L))).repr
            (a.finite w) i,
      a.eventually_integral i⟩⟩

omit [NumberField L] in
@[simp]
theorem relativeLocalAdeleCoefficient_infinite
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L))
    (w : InfinitePlace K) :
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a i).1 w =
      (Algebra.TensorProduct.basis
          w.Completion
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.infinite w) i :=
  rfl

omit [NumberField L] in
@[simp]
theorem relativeLocalAdeleCoefficient_finite
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a i).2 w =
      (Algebra.TensorProduct.basis
          (w.adicCompletion K)
          (relativeExtensionBasis
            (K := K) (L := L))).repr
          (a.finite w) i :=
  rfl

/-- Assemble a restricted family of local tensor elements into a
relative adele. -/
noncomputable def relativeAdeleOfLocalData
    (a : RelativeLocalAdeleData (K := K) (L := L)) :
    RelativeAdeleRing K L :=
  relativeAdeleOfCoefficients
    (K := K) (L := L)
    (relativeLocalAdeleCoefficient
      (K := K) (L := L) a)

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_infiniteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    relativeAdeleInfiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a.infinite w := by
  apply
    (Algebra.TensorProduct.basis
      w.Completion
      (relativeExtensionBasis
        (K := K) (L := L))).repr.injective
  apply Finsupp.ext
  intro i
  rw [relativeAdeleInfiniteComponent_basis_repr]
  have h :=
    relativeAdeleCoefficient_ofCoefficients
      (K := K) (L := L)
      (relativeLocalAdeleCoefficient
        (K := K) (L := L) a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.1 w) h

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_finiteComponent
    (a : RelativeLocalAdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    relativeAdeleFiniteComponent
        (K := K) (L := L) w
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a.finite w := by
  apply
    (Algebra.TensorProduct.basis
      (w.adicCompletion K)
      (relativeExtensionBasis
        (K := K) (L := L))).repr.injective
  apply Finsupp.ext
  intro i
  rw [relativeAdeleFiniteComponent_basis_repr]
  have h :=
    relativeAdeleCoefficient_ofCoefficients
      (K := K) (L := L)
      (relativeLocalAdeleCoefficient
        (K := K) (L := L) a) i
  exact congrArg
    (fun q : NumberField.AdeleRing (𝓞 K) K =>
      q.2.1 w) h

/-- Extract every local tensor component of a relative adele, together
with the restrictedness supplied by its base-adele coefficients. -/
noncomputable def relativeAdeleToLocalData
    (z : RelativeAdeleRing K L) :
    RelativeLocalAdeleData (K := K) (L := L) :=
  RelativeLocalAdeleData.ofBasisData
    (fun w => relativeAdeleInfiniteComponent (K := K) (L := L) w z)
    (fun w => relativeAdeleFiniteComponent (K := K) (L := L) w z)
    (fun i => by
      filter_upwards [
        (relativeAdeleCoefficient
          (K := K) (L := L) z i).2.2] with w hw
      rw [relativeAdeleFiniteComponent_basis_repr]
      change
        (relativeAdeleCoefficient
          (K := K) (L := L) z i).2.1 w ∈
            w.adicCompletionIntegers K at hw ⊢
      exact hw)

omit [NumberField L] in
@[simp]
theorem relativeAdeleOfLocalData_toLocalData
    (z : RelativeAdeleRing K L) :
    relativeAdeleOfLocalData
        (K := K) (L := L)
        (relativeAdeleToLocalData
          (K := K) (L := L) z) =
      z := by
  apply relativeAdele_ext_of_components
  · intro w
    rw [relativeAdeleOfLocalData_infiniteComponent
      (K := K) (L := L)]
    rfl
  · intro w
    rw [relativeAdeleOfLocalData_finiteComponent
      (K := K) (L := L)]
    rfl

omit [NumberField L] in
@[simp]
theorem relativeAdeleToLocalData_ofLocalData
    (a : RelativeLocalAdeleData (K := K) (L := L)) :
    relativeAdeleToLocalData
        (K := K) (L := L)
        (relativeAdeleOfLocalData
          (K := K) (L := L) a) =
      a := by
  apply RelativeLocalAdeleData.ext
  · funext w
    change
      relativeAdeleInfiniteComponent
          (K := K) (L := L) w
          (relativeAdeleOfLocalData
            (K := K) (L := L) a) =
        a.infinite w
    rw [relativeAdeleOfLocalData_infiniteComponent
      (K := K) (L := L)]
  · funext w
    change
      relativeAdeleFiniteComponent
          (K := K) (L := L) w
          (relativeAdeleOfLocalData
            (K := K) (L := L) a) =
        a.finite w
    rw [relativeAdeleOfLocalData_finiteComponent
      (K := K) (L := L)]

/-- Coordinatewise restricted local tensor families are exactly
relative adeles. -/
noncomputable def relativeAdeleEquivLocalData :
    RelativeAdeleRing K L ≃
      RelativeLocalAdeleData (K := K) (L := L) where
  toFun :=
    relativeAdeleToLocalData (K := K) (L := L)
  invFun :=
    relativeAdeleOfLocalData (K := K) (L := L)
  left_inv :=
    relativeAdeleOfLocalData_toLocalData
      (K := K) (L := L)
  right_inv :=
    relativeAdeleToLocalData_ofLocalData
      (K := K) (L := L)

/-- The local reconstruction equivalence respects the standard componentwise ring operations. -/
noncomputable def relativeAdeleRingEquivLocalData :
    RelativeAdeleRing K L ≃+* RelativeLocalAdeleData (K := K) (L := L) where
  __ := relativeAdeleEquivLocalData (K := K) (L := L)
  map_add' x y := by
    apply RelativeLocalAdeleData.ext
    · funext w
      exact (relativeAdeleInfiniteComponent (K := K) (L := L) w).map_add x y
    · funext w
      exact (relativeAdeleFiniteComponent (K := K) (L := L) w).map_add x y
  map_mul' x y := by
    apply RelativeLocalAdeleData.ext
    · funext w
      exact (relativeAdeleInfiniteComponent (K := K) (L := L) w).map_mul x y
    · funext w
      exact (relativeAdeleFiniteComponent (K := K) (L := L) w).map_mul x y
