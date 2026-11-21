/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedRing
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.LocalComponents
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Topology.Algebra.RestrictedProduct.Units
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent

/-!
# The restricted local product of a relative adele algebra

Local tensor units form the standard product of the archimedean unit
families and the finite restricted product. The comparison with global
relative ideles is the unit-group map of the relative adele ring comparison.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- Infinite tensor units together with the intrinsic finite restricted product. -/
abbrev RelativeLocalIdeleData :=
  (∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ) ×
    RelativeFiniteIdeleData (K := K) (L := L)

omit [NumberField L] in
/-- Infinite unit components of the standard local product. -/
abbrev RelativeLocalIdeleData.infinite
    (a : RelativeLocalIdeleData (K := K) (L := L)) := a.1

omit [NumberField L] in
/-- Finite unit components of the standard local product. -/
abbrev RelativeLocalIdeleData.finite
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletion K ⊗[K] L)ˣ := a.2

omit [NumberField L] in
/-- The local product inherits eventual basis integrality from its finite factor. -/
theorem RelativeLocalIdeleData.eventually_integral
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (Algebra.TensorProduct.basis (w.adicCompletion K)
        (relativeExtensionBasis (K := K) (L := L))).repr
          (a.finite w : w.adicCompletion K ⊗[K] L) i ∈
            w.adicCompletionIntegers K :=
  a.2.eventually_integral i

omit [NumberField L] in
/-- Inverse components have the same eventual basis integrality. -/
theorem RelativeLocalIdeleData.eventually_inverse_integral
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (i : RelativeAdeleBasisIndex (K := K) (L := L)) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      (Algebra.TensorProduct.basis (w.adicCompletion K)
        (relativeExtensionBasis (K := K) (L := L))).repr
          (↑((a.finite w)⁻¹) : w.adicCompletion K ⊗[K] L) i ∈
            w.adicCompletionIntegers K :=
  a.2.eventually_inverse_integral i

omit [NumberField L] in
/-- Construct the standard local product from basis-integral unit families. -/
noncomputable def RelativeLocalIdeleData.ofBasisData
    (infinite : ∀ w : InfinitePlace K, (w.Completion ⊗[K] L)ˣ)
    (finite : ∀ w : HeightOneSpectrum (𝓞 K), (w.adicCompletion K ⊗[K] L)ˣ)
    (hintegral : ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis (w.adicCompletion K)
          (relativeExtensionBasis (K := K) (L := L))).repr
            (finite w : w.adicCompletion K ⊗[K] L) i ∈
              w.adicCompletionIntegers K)
    (hinverse : ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
        (Algebra.TensorProduct.basis (w.adicCompletion K)
          (relativeExtensionBasis (K := K) (L := L))).repr
            (↑((finite w)⁻¹) : w.adicCompletion K ⊗[K] L) i ∈
              w.adicCompletionIntegers K) :
    RelativeLocalIdeleData (K := K) (L := L) :=
  ⟨infinite, RelativeFiniteIdeleData.ofBasisData finite hintegral hinverse⟩

omit [NumberField L] in
/-- Local restricted unit families are determined by their component values. -/
@[ext]
theorem RelativeLocalIdeleData.ext
    {a b : RelativeLocalIdeleData (K := K) (L := L)}
    (hinfinite : a.infinite = b.infinite)
    (hfinite : a.finite = b.finite) : a = b :=
  Prod.ext hinfinite (Subtype.ext hfinite)

/-- Units of the restricted local ring are the standard restricted local unit product. -/
noncomputable def relativeLocalAdeleUnitsEquiv :
    (RelativeLocalAdeleData (K := K) (L := L))ˣ ≃*
      RelativeLocalIdeleData (K := K) (L := L) :=
  MulEquiv.prodUnits.trans
    (MulEquiv.piUnits.prodCongr
      (RestrictedProduct.unitsEquiv
        (ι := HeightOneSpectrum (𝓞 K))
        (S := fun w : HeightOneSpectrum (𝓞 K) => Subring (w.adicCompletion K ⊗[K] L))
        (B := relativeLocalTensorDecompositionIntegralSubring (K := K) (L := L))
        (𝓕 := Filter.cofinite)
        (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K ⊗[K] L)))

/-- Forget local invertibility while retaining the same restricted value family. -/
noncomputable def RelativeLocalIdeleData.value
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeLocalAdeleData (K := K) (L := L) :=
  ((relativeLocalAdeleUnitsEquiv (K := K) (L := L)).symm a).val

/-- The pointwise inverse family in the same restricted local ring. -/
noncomputable def RelativeLocalIdeleData.inverse
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeLocalAdeleData (K := K) (L := L) :=
  (((relativeLocalAdeleUnitsEquiv (K := K) (L := L)).symm a)⁻¹).val

/-- The local idele comparison is induced by the relative adele ring comparison. -/
noncomputable def relativeIdeleMulEquivLocalData :
    RelativeIdeleGroup K L ≃* RelativeLocalIdeleData (K := K) (L := L) :=
  (Units.mapEquiv
    (relativeAdeleRingEquivLocalData (K := K) (L := L)).toMulEquiv).trans
      (relativeLocalAdeleUnitsEquiv (K := K) (L := L))

/-- Extract the complete restricted local-unit family of a relative idele. -/
noncomputable def relativeIdeleToLocalData
    (z : RelativeIdeleGroup K L) :
    RelativeLocalIdeleData (K := K) (L := L) :=
  relativeIdeleMulEquivLocalData (K := K) (L := L) z

/-- Assemble restricted local units by the inverse of the same ring-induced comparison. -/
noncomputable def relativeIdeleOfLocalData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    RelativeIdeleGroup K L :=
  (relativeIdeleMulEquivLocalData (K := K) (L := L)).symm a

omit [NumberField L] in
@[simp]
theorem relativeIdeleToLocalData_infinite
    (z : RelativeIdeleGroup K L) (w : InfinitePlace K) :
    (relativeIdeleToLocalData (K := K) (L := L) z).infinite w =
      RelativeIdeleGroup.infiniteComponent (K := K) (L := L) w z :=
  rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleToLocalData_finite
    (z : RelativeIdeleGroup K L) (w : HeightOneSpectrum (𝓞 K)) :
    (relativeIdeleToLocalData (K := K) (L := L) z).finite w =
      RelativeIdeleGroup.finiteComponent (K := K) (L := L) w z :=
  rfl

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_infiniteComponent
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : InfinitePlace K) :
    RelativeIdeleGroup.infiniteComponent (K := K) (L := L) w
        (relativeIdeleOfLocalData (K := K) (L := L) a) = a.infinite w := by
  apply Units.ext
  exact relativeAdeleOfLocalData_infiniteComponent a.value w

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_finiteComponent
    (a : RelativeLocalIdeleData (K := K) (L := L))
    (w : HeightOneSpectrum (𝓞 K)) :
    RelativeIdeleGroup.finiteComponent (K := K) (L := L) w
        (relativeIdeleOfLocalData (K := K) (L := L) a) = a.finite w := by
  apply Units.ext
  exact relativeAdeleOfLocalData_finiteComponent a.value w

omit [NumberField L] in
@[simp]
theorem relativeIdeleOfLocalData_toLocalData (z : RelativeIdeleGroup K L) :
    relativeIdeleOfLocalData (K := K) (L := L)
      (relativeIdeleToLocalData (K := K) (L := L) z) = z :=
  (relativeIdeleMulEquivLocalData (K := K) (L := L)).symm_apply_apply z

omit [NumberField L] in
@[simp]
theorem relativeIdeleToLocalData_ofLocalData
    (a : RelativeLocalIdeleData (K := K) (L := L)) :
    relativeIdeleToLocalData (K := K) (L := L)
      (relativeIdeleOfLocalData (K := K) (L := L) a) = a :=
  (relativeIdeleMulEquivLocalData (K := K) (L := L)).apply_symm_apply a

/-- The underlying local-data equivalence of the ring-induced unit comparison. -/
noncomputable def relativeIdeleEquivLocalData :
    RelativeIdeleGroup K L ≃ RelativeLocalIdeleData (K := K) (L := L) :=
  (relativeIdeleMulEquivLocalData (K := K) (L := L)).toEquiv

omit [NumberField L] in
@[simp]
theorem relativeIdeleMulEquivLocalData_apply (z : RelativeIdeleGroup K L) :
    relativeIdeleMulEquivLocalData (K := K) (L := L) z =
      relativeIdeleToLocalData (K := K) (L := L) z := rfl

omit [NumberField L] in
@[simp]
theorem RelativeLocalIdeleData.infinite_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L)) (w : InfinitePlace K) :
    (a * b).infinite w = a.infinite w * b.infinite w := rfl

omit [NumberField L] in
@[simp]
theorem RelativeLocalIdeleData.finite_mul
    (a b : RelativeLocalIdeleData (K := K) (L := L)) (w : HeightOneSpectrum (𝓞 K)) :
    (a * b).finite w = a.finite w * b.finite w := rfl
