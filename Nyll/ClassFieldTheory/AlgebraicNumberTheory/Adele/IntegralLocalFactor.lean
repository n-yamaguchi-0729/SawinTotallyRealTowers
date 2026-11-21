/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.FiniteLocalFactor

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.IdeleSupport
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Localization
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.CompletionIntegers
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.Lattice
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.FinitePlaceCompletion
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.IntegralTensorSupport.LocalTensorDecomposition
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Group.Submonoid.Units
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion

/-!
# Integral finite local factors of the relative idele group

For a finite place `w` of the base field, the canonical local tensor decomposition identifies
`K_w ⊗_K L` with the product of the completions of `L` above `w`.
This file packages each projection as an actual ring homomorphism and
defines the subgroup of tensor units whose value and inverse are integral
in every completion factor.  Thus the integrality predicate used for the
restricted product is closed under all group operations for structural,
rather than coordinate-dependent, reasons.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section


open AlgebraicNumberTheory.Valuations
open LocalClassFieldTheory

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
/-- The completion equivalence induced by conjugation preserves the
norm exactly. -/
theorem conjugateExtensionCompletionRingEquiv_norm_eq
    (vK : AbsoluteValue K ℝ)
    (wL : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (x :
      (absoluteValueExtensionConjugate
        vK wL σ).1.Completion) :
    ‖conjugateExtensionCompletionRingEquiv vK wL σ x‖ =
      ‖x‖ := by
  change ‖conjugateCompletionRingEquiv wL.1 σ x‖ = ‖x‖
  let w := wL.1
  have h := (AbsoluteValue.Completion.isometry_ofCompletion w).comp
    ((UniformSpace.Completion.isometry_mapRingHom (conjugateWithAbsRingEquiv_isometry w σ)).comp
      (AbsoluteValue.Completion.isometry_toCompletion (absoluteValueConjugate w σ)))
  have hfun (y : (absoluteValueConjugate w σ).Completion) :
      conjugateCompletionRingEquiv w σ y = AbsoluteValue.Completion.ofCompletion
        (UniformSpace.Completion.map (conjugateWithAbsRingEquiv w σ)
          (AbsoluteValue.Completion.toCompletion y)) := by
    simp only [conjugateCompletionRingEquiv, RingEquiv.trans_apply,
      AbsoluteValue.Completion.equiv_apply, AbsoluteValue.Completion.equiv_symm_apply,
      UniformSpace.Completion.mapRingEquiv_apply]
  have hiso : Isometry (conjugateCompletionRingEquiv w σ) :=
    Isometry.of_dist_eq fun a b => (congrArg₂ dist (hfun a) (hfun b)).trans (h.dist_eq a b)
  exact hiso.norm_map_of_map_zero (map_zero (conjugateCompletionRingEquiv w σ)) x

omit [NumberField K] [NumberField L]
    [FiniteDimensional K L] in
/-- The conjugate-completion equivalence identifies the two valuation
rings. -/
theorem
    conjugateExtensionCompletionRingEquiv_mem_integers_iff
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (wL : AbsoluteValueExtension vK L)
    (σ : L ≃ₐ[K] L)
    (x :
      (absoluteValueExtensionConjugate
        vK wL σ).1.Completion) :
    conjugateExtensionCompletionRingEquiv vK wL σ x ∈
        absoluteValueCompletionIntegers wL.1
          (absoluteValueExtension_isNonarchimedean
            vK hvK wL) ↔
      x ∈
        absoluteValueCompletionIntegers
          (absoluteValueExtensionConjugate
            vK wL σ).1
          (absoluteValueExtension_isNonarchimedean
            vK hvK
            (absoluteValueExtensionConjugate
              vK wL σ)) := by
  rw [mem_absoluteValueCompletionIntegers_iff,
    mem_absoluteValueCompletionIntegers_iff,
    conjugateExtensionCompletionRingEquiv_norm_eq]

omit [NumberField L] in
/-- Galois conjugation sends the component at `wL` to the component at
the conjugate extension, transported by the canonical completion
isometry. -/
theorem finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation
    (w : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (HeightOneSpectrum.adicAbv K w) L)
    (σ : L ≃ₐ[K] L)
    (x : w.adicCompletion K ⊗[K] L) :
    finitePlaceLocalTensorDecompositionComponent
        (K := K) (L := L) w wL
        (scalarTensorConjugation
          (K := K) (L := L)
          (A := w.adicCompletion K) σ x) =
      conjugateExtensionCompletionRingEquiv
        (HeightOneSpectrum.adicAbv K w) wL σ
        (finitePlaceLocalTensorDecompositionComponent
          (K := K) (L := L) w
          (absoluteValueExtensionConjugate
            (HeightOneSpectrum.adicAbv K w) wL σ) x) := by
  let vK := HeightOneSpectrum.adicAbv K w
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial w
  let : ∀ u : AbsoluteValueExtension vK L,
      Algebra vK.Completion u.1.Completion :=
    fun u =>
      AbsoluteValue.completionAlgebra vK u.1 u.2
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
      rw [map_add, finitePlaceLocalTensorDecompositionComponent_add,
        finitePlaceLocalTensorDecompositionComponent_add, map_add, hx, hy]
  | tmul a b =>
      rw [scalarTensorConjugation_tmul,
        finitePlaceLocalTensorDecompositionComponent_tmul,
        finitePlaceLocalTensorDecompositionComponent_tmul,
        map_mul]
      change
        algebraMap vK.Completion wL.1.Completion
              ((finitePlaceCompletionAlgEquiv
                (K := K) w).symm a) *
            AbsoluteValue.toCompletion wL.1 (σ b) =
          conjugateExtensionCompletionRingEquiv vK wL σ
                (algebraMap vK.Completion
                  (absoluteValueExtensionConjugate
                    vK wL σ).1.Completion
                  ((finitePlaceCompletionAlgEquiv
                    (K := K) w).symm a)) *
            conjugateExtensionCompletionRingEquiv vK wL σ
              (AbsoluteValue.toCompletion
                (absoluteValueExtensionConjugate
                  vK wL σ).1 b)
      rw [conjugateExtensionCompletionRingEquiv_algebraMap,
        conjugateExtensionCompletionRingEquiv_toCompletion]

omit [NumberField L] in
/-- Valuation-ring integrality of a tensor element is preserved by
Galois conjugation. -/
theorem relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    {x : w.adicCompletion K ⊗[K] L}
    (hx : RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w x) :
    RelativeLocalTensorDecompositionIntegralAt
      (K := K) (L := L) w
      (scalarTensorConjugation
        (K := K) (L := L)
        (A := w.adicCompletion K) σ x) := by
  intro wL
  rw [finitePlaceLocalTensorDecompositionComponent_scalarTensorConjugation]
  exact
    (conjugateExtensionCompletionRingEquiv_mem_integers_iff
      (K := K) (L := L)
      (vK := HeightOneSpectrum.adicAbv K w)
      (hvK :=
        HeightOneSpectrum.isNonarchimedean_adicAbv K w)
      (wL := wL) (σ := σ) _).2
      (hx
        (absoluteValueExtensionConjugate
          (HeightOneSpectrum.adicAbv K w) wL σ))

omit [NumberField L] in
/-- The integral tensor-unit condition is stable under the natural
Galois action. -/
theorem relativeLocalTensorDecompositionIntegralUnitAt_smul
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (x : (w.adicCompletion K ⊗[K] L)ˣ)
    (hx : RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w x) :
    let := scalarTensorUnitsAction
      (K := K) (L := L)
      (A := w.adicCompletion K)
    RelativeLocalTensorDecompositionIntegralUnitAt
      (K := K) (L := L) w (σ • x) := by
  intro sharedOwner1
  constructor
  · rw [scalarTensorUnitsAction_coe]
    exact
      relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
        (K := K) (L := L) w σ hx.1
  · rw [← smul_inv', scalarTensorUnitsAction_coe]
    exact
      relativeLocalTensorDecompositionIntegralAt_scalarTensorConjugation
        (K := K) (L := L) w σ hx.2

/-- The restricted Galois action on the integral tensor-unit
subgroup. -/
@[implicit_reducible]
noncomputable def
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction
    (w : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction
      (L ≃ₐ[K] L)
      (relativeLocalTensorDecompositionIntegralUnitSubgroup
        (K := K) (L := L) w) := by
  letI := scalarTensorUnitsAction
    (K := K) (L := L)
    (A := w.adicCompletion K)
  exact
    { smul := fun σ x =>
        ⟨σ • (x :
            (w.adicCompletion K ⊗[K] L)ˣ),
          by
            rw [mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff]
            have hx :
                RelativeLocalTensorDecompositionIntegralUnitAt
                  (K := K) (L := L) w
                  (x : (w.adicCompletion K ⊗[K] L)ˣ) :=
              (mem_relativeLocalTensorDecompositionIntegralUnitSubgroup_iff
                (K := K) (L := L) w x).1 x.property
            exact
              relativeLocalTensorDecompositionIntegralUnitAt_smul
                (K := K) (L := L) w σ x hx⟩
      one_smul := by
        intro x
        apply Subtype.ext
        change
          (1 : L ≃ₐ[K] L) •
              (x : (w.adicCompletion K ⊗[K] L)ˣ) =
            (x : (w.adicCompletion K ⊗[K] L)ˣ)
        exact one_smul (L ≃ₐ[K] L) _
      mul_smul := by
        intro σ τ x
        apply Subtype.ext
        exact mul_smul σ τ
          (x : (w.adicCompletion K ⊗[K] L)ˣ)
      smul_one := by
        intro σ
        apply Subtype.ext
        change
          σ • (1 : (w.adicCompletion K ⊗[K] L)ˣ) = 1
        exact smul_one σ
      smul_mul := by
        intro σ x y
        apply Subtype.ext
        exact smul_mul' σ
          (x : (w.adicCompletion K ⊗[K] L)ˣ)
          (y : (w.adicCompletion K ⊗[K] L)ˣ) }

omit [NumberField L] in
@[simp]
theorem
    relativeLocalTensorDecompositionIntegralUnitSubgroupAction_coe
    (w : HeightOneSpectrum (𝓞 K))
    (σ : L ≃ₐ[K] L)
    (x : relativeLocalTensorDecompositionIntegralUnitSubgroup
      (K := K) (L := L) w) :
    letI :=
      relativeLocalTensorDecompositionIntegralUnitSubgroupAction
        (K := K) (L := L) w
    ((σ • x :
        relativeLocalTensorDecompositionIntegralUnitSubgroup
          (K := K) (L := L) w) :
      (w.adicCompletion K ⊗[K] L)ˣ) =
      letI := scalarTensorUnitsAction
        (K := K) (L := L)
        (A := w.adicCompletion K)
      σ •
        (x : (w.adicCompletion K ⊗[K] L)ˣ) :=
  rfl
