/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RelativeSupport
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent

/-!
# Finite coefficient support for relative ideles

This file supplies the finite-support input for the actual scalar-extension model

`𝔸_K ⊗[K] L`.

Fixing the canonical chosen `K`-basis of `L`, every relative adele has
finitely many base-adele coefficients.  For a relative idele we take
the union of the nonintegral finite places of the coefficients of the
idele and of its inverse.  Outside this finite set both local tensor
components therefore lie in the lattice spanned by that basis over
the local valuation ring.

This produces the finite support from a basis lattice.  Passing from
that lattice to the product of local integer rings additionally requires
integral compatibility of the relative tensor decomposition.
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

/-- The exact coefficient support of a relative idele contains the
exceptional places of the idele and its inverse. -/
noncomputable def relativeIdeleCoefficientSupport
    (z : RelativeIdeleGroup K L) :
    Finset (HeightOneSpectrum (𝓞 K)) := by
  classical
  exact
    relativeAdeleCoefficientSupport
        (K := K) (L := L)
        (z : RelativeAdeleRing K L) ∪
      relativeAdeleCoefficientSupport
        (K := K) (L := L)
        ((z⁻¹ : RelativeIdeleGroup K L) :
          RelativeAdeleRing K L)

omit [NumberField L] in
@[simp]
theorem mem_relativeIdeleCoefficientSupport_iff
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    w ∈ relativeIdeleCoefficientSupport
        (K := K) (L := L) z ↔
      (∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            (z : RelativeAdeleRing K L) i).2 w ∉
          w.adicCompletionIntegers K) ∨
      (∃ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            ((z⁻¹ : RelativeIdeleGroup K L) :
              RelativeAdeleRing K L) i).2 w ∉
          w.adicCompletionIntegers K) := by
  classical
  simp only [relativeIdeleCoefficientSupport, Finset.mem_union,
    mem_relativeAdeleCoefficientSupport_iff]

omit [NumberField L] in
/-- Outside the exact coefficient support, every coefficient of both
the relative idele and its inverse is integral at the given finite
place. -/
theorem relativeIdele_coefficients_integral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      (relativeAdeleCoefficient
          (K := K) (L := L)
          (z : RelativeAdeleRing K L) i).2 w ∈
        w.adicCompletionIntegers K) ∧
    (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
      (relativeAdeleCoefficient
          (K := K) (L := L)
          ((z⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) i).2 w ∈
        w.adicCompletionIntegers K) := by
  constructor
  · intro i
    by_contra hi
    apply hw
    exact
      (mem_relativeIdeleCoefficientSupport_iff
        (K := K) (L := L) z w).2
        (Or.inl ⟨i, hi⟩)
  · intro i
    by_contra hi
    apply hw
    exact
      (mem_relativeIdeleCoefficientSupport_iff
        (K := K) (L := L) z w).2
        (Or.inr ⟨i, hi⟩)

omit [NumberField L] in
/-- The exact support is the least finset outside which all
coefficients of the idele and its inverse are integral. -/
theorem relativeIdeleCoefficientSupport_minimal
    (z : RelativeIdeleGroup K L)
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hS :
      ∀ w, w ∉ S →
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              (z : RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K) ∧
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              ((z⁻¹ : RelativeIdeleGroup K L) :
                RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K)) :
    relativeIdeleCoefficientSupport
        (K := K) (L := L) z ⊆ S := by
  intro w hw
  by_contra hwS
  obtain hbad | hbad :=
    (mem_relativeIdeleCoefficientSupport_iff
      (K := K) (L := L) z w).1 hw
  · obtain ⟨i, hi⟩ := hbad
    exact hi ((hS w hwS).1 i)
  · obtain ⟨i, hi⟩ := hbad
    exact hi ((hS w hwS).2 i)

omit [NumberField L] in
/-- The finite component of a relative idele is given by the evaluated
base-adele coefficients. -/
theorem relativeIdele_finiteComponent_eq_sum_tmul_coefficients
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K)) :
    ((RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z :
        (w.adicCompletion K ⊗[K] L)ˣ) :
        w.adicCompletion K ⊗[K] L) =
      ∑ i : RelativeAdeleBasisIndex (K := K) (L := L),
        (relativeAdeleCoefficient
            (K := K) (L := L)
            (z : RelativeAdeleRing K L) i).2 w ⊗ₜ[K]
          relativeExtensionBasis (K := K) (L := L) i := by
  rw [RelativeIdeleGroup.finiteComponent_coe]
  exact
    relativeAdeleFiniteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L)
      (z : RelativeAdeleRing K L) w

omit [NumberField L] in
/-- Outside the coefficient support, the actual finite component lies
in the local lattice spanned by the chosen extension basis. -/
theorem relativeIdele_finiteComponent_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L)
          (z : RelativeAdeleRing K L) i).2 w,
        (relativeIdele_coefficients_integral_of_notMem
          (K := K) (L := L) z w hw).1 i⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeIdele_finiteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L) z w

omit [NumberField L] in
/-- Outside the same support, the actual finite component of the
inverse lies in the same local basis lattice. -/
theorem relativeIdele_inverse_finiteComponent_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w
          (z⁻¹ : RelativeIdeleGroup K L) :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L) := by
  let c :
      ∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
        w.adicCompletionIntegers K :=
    fun i =>
      ⟨(relativeAdeleCoefficient
          (K := K) (L := L)
          ((z⁻¹ : RelativeIdeleGroup K L) :
            RelativeAdeleRing K L) i).2 w,
        (relativeIdele_coefficients_integral_of_notMem
          (K := K) (L := L) z w hw).2 i⟩
  refine ⟨c, ?_⟩
  simpa only [c, Subtype.coe_mk] using
    relativeIdele_finiteComponent_eq_sum_tmul_coefficients
      (K := K) (L := L)
      (z⁻¹ : RelativeIdeleGroup K L) w

omit [NumberField L] in
/-- Equivalently, the inverse of the actual local unit component lies
in the same basis lattice outside the coefficient support. -/
theorem relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralAt
      (K := K) (L := L) w
      ((((RelativeIdeleGroup.finiteComponent
          (K := K) (L := L) w z)⁻¹ :
          (w.adicCompletion K ⊗[K] L)ˣ) :
          w.adicCompletion K ⊗[K] L)) := by
  simpa using
    relativeIdele_inverse_finiteComponent_basisIntegral_of_notMem
      (K := K) (L := L) z w hw

omit [NumberField L] in
/-- Thus the actual local unit component is basis-integral outside the
explicit coefficient support. -/
theorem relativeIdele_finiteComponent_basisIntegralUnit_of_notMem
    (z : RelativeIdeleGroup K L)
    (w : HeightOneSpectrum (𝓞 K))
    (hw : w ∉ relativeIdeleCoefficientSupport
      (K := K) (L := L) z) :
    RelativeBasisIntegralUnitAt
      (K := K) (L := L) w
      (RelativeIdeleGroup.finiteComponent
        (K := K) (L := L) w z) :=
  ⟨relativeIdele_finiteComponent_basisIntegral_of_notMem
      (K := K) (L := L) z w hw,
    relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
      (K := K) (L := L) z w hw⟩

omit [NumberField L] in
/-- A source-producing finite-support theorem: one explicit
minimal finset simultaneously controls the local basis integrality of
the relative idele and its inverse. -/
theorem exists_relativeIdele_coefficientSupport
    (z : RelativeIdeleGroup K L) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      (∀ w, w ∉ S →
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              (z : RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K) ∧
        (∀ i : RelativeAdeleBasisIndex (K := K) (L := L),
          (relativeAdeleCoefficient
              (K := K) (L := L)
              ((z⁻¹ : RelativeIdeleGroup K L) :
                RelativeAdeleRing K L) i).2 w ∈
            w.adicCompletionIntegers K)) ∧
      (∀ w, w ∉ S →
        RelativeBasisIntegralAt
          (K := K) (L := L) w
          ((RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w z :
              (w.adicCompletion K ⊗[K] L)ˣ) :
              w.adicCompletion K ⊗[K] L) ∧
        RelativeBasisIntegralAt
          (K := K) (L := L) w
          ((((RelativeIdeleGroup.finiteComponent
              (K := K) (L := L) w z)⁻¹ :
              (w.adicCompletion K ⊗[K] L)ˣ) :
              w.adicCompletion K ⊗[K] L))) := by
  refine
    ⟨relativeIdeleCoefficientSupport
        (K := K) (L := L) z, ?_, ?_⟩
  · intro w hw
    exact
      relativeIdele_coefficients_integral_of_notMem
        (K := K) (L := L) z w hw
  · intro w hw
    exact
      ⟨relativeIdele_finiteComponent_basisIntegral_of_notMem
          (K := K) (L := L) z w hw,
        relativeIdele_finiteComponent_inv_basisIntegral_of_notMem
          (K := K) (L := L) z w hw⟩
