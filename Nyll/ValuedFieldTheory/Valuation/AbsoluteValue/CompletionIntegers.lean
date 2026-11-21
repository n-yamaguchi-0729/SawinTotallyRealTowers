/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Module.NatInt
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.ExponentialValuation
public import Nyll.ValuedFieldTheory.Valuation.Henselian.Complete
public import Nyll.ValuedFieldTheory.Valuation.Completion.TensorProductDecomposition
public import Nyll.ValuedFieldTheory.Valuation.Completion.DegreeNormTrace
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Nonarchimedean
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations
public import Nyll.ValuedFieldTheory.Valuation.Henselian.Core

/-!
# Valuation rings in absolute-value completions

Nonarchimedean absolute values extend to complete valued fields. Their closed
unit balls are valuation rings, and finite separable extension-completion
valuation rings are integral over the corresponding base valuation ring.
-/

@[expose] public section

open scoped TensorProduct NNReal

noncomputable section


open AlgebraicNumberTheory.Valuations

universe u v

variable
    {K : Type u} {L : Type v}
    [Field K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L]

/-- A nonarchimedean real absolute value, regarded as a valuation with
values in the nonnegative reals. -/
noncomputable def realAbsoluteValueValuation
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    Valuation F NNReal where
  toFun x := ⟨vF x, vF.nonneg x⟩
  map_one' := by
    ext
    exact vF.map_one
  map_zero' := by
    ext
    exact vF.map_zero
  map_mul' x y := by
    ext
    exact vF.map_mul x y
  map_add_le_max' x y := by
    change vF (x + y) ≤ max (vF x) (vF y)
    exact hvF x y

/-- The following two lemmas expose the valuation-subring interface used by later modules. -/
@[simp]
theorem realAbsoluteValueValuation_apply
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (x : F) :
    ((realAbsoluteValueValuation vF hvF x : NNReal) : ℝ) =
      vF x :=
  rfl

/-- Every extension of a nonarchimedean absolute value is again
nonarchimedean.  For algebraic extensions this follows already from
the bounded-natural-number criterion and the extension identity. -/
theorem absoluteValueExtension_isNonarchimedean
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (w : AbsoluteValueExtension vF E) :
    IsNonarchimedean (w.1 : E → ℝ) := by
  rw [AbsoluteValue.isNonarchimedean_iff_bounded_nat]
  refine ⟨1, ?_⟩
  intro n
  calc
    w.1 (n : E) =
        w.1 (algebraMap F E (n : F)) := by rw [map_natCast (algebraMap F E)]
    _ = vF (n : F) := w.2 (n : F)
    _ ≤ 1 :=
      hvF.apply_natCast_le_one (map_zero_le vF 1) (map_one vF)

/-- An element integral over `ℤ` lies in the valuation subring of
every nonarchimedean real absolute value. -/
theorem absoluteValue_le_one_of_isIntegral
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    {x : F} (hx : IsIntegral ℤ x) :
    vF x ≤ 1 := by
  let ν : Valuation F NNReal :=
    realAbsoluteValueValuation vF hvF
  let V : ValuationSubring F := ν.valuationSubring
  let : IsIntegrallyClosedIn V F :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn F).1
      inferInstance
  have hxV : IsIntegral V x :=
    hx.tower_top
  obtain ⟨y, hy⟩ :=
    (IsIntegrallyClosedIn.isIntegral_iff).1 hxV
  have hν : x ∈ V := by
    rw [← hy, ValuationSubring.algebraMap_apply]
    exact y.property
  change
    realAbsoluteValueValuation vF hvF x ≤ 1 at hν
  exact_mod_cast hν

/-- The valuation ring in the completion of a nonarchimedean
real-absolute-valued field. -/
noncomputable def absoluteValueCompletionIntegers
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ)) :
    ValuationSubring vF.Completion :=
  (realAbsoluteValueValuation
    (AbsoluteValue.completionAbsoluteValue vF)
    (AbsoluteValue.completionAbsoluteValue_isNonarchimedean
      vF hvF)).valuationSubring

/-- Membership in the absolute-value completion integers is the valuation bound. -/
@[simp]
theorem mem_absoluteValueCompletionIntegers_iff
    {F : Type*} [Field F]
    (vF : AbsoluteValue F ℝ)
    (hvF : IsNonarchimedean (vF : F → ℝ))
    (x : vF.Completion) :
    x ∈ absoluteValueCompletionIntegers vF hvF ↔
      ‖x‖ ≤ 1 :=
  Iff.rfl

/-- An element of an extension-completion valuation ring is integral
over the valuation ring in the base completion.  This is the
integral-closure characterization for complete henselian valued
fields, expressed in the absolute-value completion model used by
the canonical local tensor decomposition. -/
theorem isIntegral_over_baseCompletionIntegers_of_mem
    [Algebra.IsSeparable K L]
    (vK : AbsoluteValue K ℝ)
    (hvK : IsNonarchimedean (vK : K → ℝ))
    (hvK0 : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK L)
    {x : w.1.Completion}
    (hx : x ∈ absoluteValueCompletionIntegers w.1
      (absoluteValueExtension_isNonarchimedean vK hvK w)) :
    letI := AbsoluteValue.completionAlgebra vK w.1 w.2
    IsIntegral (absoluteValueCompletionIntegers vK hvK) x := by
  let hw : IsNonarchimedean (w.1 : L → ℝ) :=
    absoluteValueExtension_isNonarchimedean vK hvK w
  let aC := AbsoluteValue.completionAbsoluteValue vK
  let bC := AbsoluteValue.completionAbsoluteValue w.1
  let haC : LubinTate.Valuations.NonarchimedeanAbsoluteValue aC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat aC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean vK hvK)
  let hbC : LubinTate.Valuations.NonarchimedeanAbsoluteValue bC :=
    (AbsoluteValue.isNonarchimedean_iff_bounded_nat bC).1
      (AbsoluteValue.completionAbsoluteValue_isNonarchimedean w.1 hw)
  let va :=
    absoluteValueExponentialValuation aC haC
  let vb :=
    absoluteValueExponentialValuation bC hbC
  let : Algebra vK.Completion w.1.Completion :=
    AbsoluteValue.completionAlgebra vK w.1 w.2
  let : Module.Finite vK.Completion w.1.Completion :=
    completionModuleFinite vK hvK0 w
  let : Algebra.IsAlgebraic vK.Completion w.1.Completion :=
    Algebra.IsAlgebraic.of_finite vK.Completion w.1.Completion
  have hVaAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va =
        absoluteValueValuationSubring aC haC :=
    associatedAbsoluteValue_valuationSubring_eq
      va (Real.exp 1) aC haC
        (absoluteValueExponentialValuation_associated aC haC)
  have hVbAbs :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vb =
        absoluteValueValuationSubring bC hbC :=
    associatedAbsoluteValue_valuationSubring_eq
      vb (Real.exp 1) bC hbC
        (absoluteValueExponentialValuation_associated bC hbC)
  have hVa :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring va =
        absoluteValueCompletionIntegers vK hvK := by
    rw [hVaAbs]
    ext y
    rw [mem_absoluteValueValuationSubring_iff,
      mem_absoluteValueCompletionIntegers_iff]
    rfl
  have hVb :
      LubinTate.Valuations.exponentialValuationSubringAsValuationSubring vb =
        absoluteValueCompletionIntegers w.1 hw := by
    rw [hVbAbs]
    ext y
    rw [mem_absoluteValueValuationSubring_iff,
      mem_absoluteValueCompletionIntegers_iff]
    rfl
  have hhensAbs :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (absoluteValueValuationSubring aC haC).valuation :=
    henselianValuation_of_complete aC
      ((absoluteValueCompleteness_completeSpace_withAbs_iff_complete aC).1
        (AbsoluteValue.completionAbsoluteValue_complete vK))
      haC
  have hhens :
      ValuationTheory.DiscreteValuationField.HenselianValuationByFactorization
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
          va).valuation := by
    rw [hVaAbs]
    exact hhensAbs
  have hExt :
      ∀ y : vK.Completion,
        bC (algebraMap vK.Completion w.1.Completion y) = aC y :=
    AbsoluteValue.completionAbsoluteValue_extends vK w.1 w.2
  have hclosure :=
    exponentialValuationSubring_eq_integralClosure_of_henselian
      va vb
      (absoluteValueExponentialValuation_extends
        aC bC haC hbC hExt)
      hhens
  rw [hVa, hVb] at hclosure
  rw [← mem_integralClosure_iff]
  change x ∈
    (integralClosure
      (absoluteValueCompletionIntegers vK hvK) w.1.Completion).toSubring
  rw [← hclosure]
  exact hx
