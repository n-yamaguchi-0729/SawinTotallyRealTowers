/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.UnramifiedCriterion
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Unramified field extensions of a discrete valuation ring

For a finite separable extension of a DVR's fraction field, unramifiedness
means that every maximal prime of the integral closure has ramification
index one and separable residue extension. This is the unramified case of
[Stacks Project, Tag 09E9](https://stacks.math.columbia.edu/tag/09E9).

We prove that these residue and ramification conditions make the actual
integral closure finite étale. Its base change to the fraction field is
canonically the original field extension. These are the algebraic inputs
to the codimension-one step of
[Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W).
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

universe u v w

namespace SchemeTheory

/-- The residue-field and ramification-index condition for a field extension
to be unramified with respect to a DVR. In applications the extension of the
fraction field is finite separable. Every maximal prime of the integral
closure contracts to the maximal ideal of the base DVR. -/
def IsUnramifiedOverDVR (R : Type u) (L : Type w)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field L] [Algebra R L] : Prop :=
  ∀ (P : Ideal (integralClosure R L)) [P.IsMaximal],
    let : Algebra (Localization.AtPrime (P.under R)) (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver (P.under R) P
    Algebra.IsSeparable (P.under R).ResidueField P.ResidueField ∧
      Ideal.ramificationIdx' (P.under R) P = 1

/-- The normalization of a DVR in a finite separable fraction-field extension
is finite étale when the ramification indices are one and all residue
extensions are separable. -/
theorem finite_etale_integralClosure_of_unramifiedOverDVR
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : IsUnramifiedOverDVR R L) :
    Module.Finite R (integralClosure R L) ∧
      Algebra.Etale R (integralClosure R L) := by
  let B := integralClosure R L
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hRL
  have hfinite : Module.Finite R B := IsIntegralClosure.finite R K L B
  have hfree : Module.Free R B := IsIntegralClosure.module_free R K L B
  have hDedekind : IsDedekindDomain B := integralClosure.isDedekindDomain R K L
  have hlocal (P : Ideal B) [P.IsMaximal] : Algebra.IsUnramifiedAt R P := by
    have hbase : P.under R = IsLocalRing.maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal inferInstance
    have hm : IsLocalRing.maximalIdeal R ≠ ⊥ := by
      intro heq
      exact IsDiscreteValuationRing.not_isField R
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr heq)
    have hP : P ≠ ⊥ :=
      Ideal.ne_bot_of_liesOver_of_ne_bot (hbase ▸ hm) P
    exact (TameAbhyankar.SGA1.isUnramifiedAt_iff_residue_isSeparable_and_ramificationIdx_eq_one
      (R := R) (S := B) hP).mpr (h P)
  have hDifferentials : Subsingleton Ω[B⁄R] := by
    apply Module.subsingleton_of_localization_maximal
      (fun (P : Ideal B) (_ : P.IsMaximal) => Ω[(Localization.AtPrime P)⁄R])
      (fun (P : Ideal B) (_ : P.IsMaximal) =>
        KaehlerDifferential.map R R B (Localization.AtPrime P))
    intro P hP
    have hUnramified : Algebra.IsUnramifiedAt R P := hlocal P
    infer_instance
  have hUnramified : Algebra.FormallyUnramified R B := ⟨hDifferentials⟩
  have hPresentation : Module.FinitePresentation R B :=
    Module.finitePresentation_of_projective R B
  exact ⟨hfinite, Algebra.Etale.of_formallyUnramified_of_flat⟩

/-- The generic fibre of the actual integral closure is the original
algebraic field extension, with its given fraction-field algebra structure. -/
def integralClosureGenericFiberEquiv
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [Algebra.IsAlgebraic K L] :
    K ⊗[R] integralClosure R L ≃ₐ[K] L := by
  have hloc : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure R L) R⁰) L :=
    IsIntegralClosure.isLocalization R K L (integralClosure R L)
  have hpush : Algebra.IsPushout R (integralClosure R L) K L :=
    Algebra.isPushout_of_isLocalization R⁰ K (integralClosure R L) L
  have : Algebra.IsPushout R K (integralClosure R L) L := hpush.symm
  exact Algebra.IsPushout.equiv R K (integralClosure R L) L

/-- The generic-fibre comparison multiplies a fraction by the integral element. -/
theorem integralClosureGenericFiberEquiv_tmul
    (R : Type u) (K : Type v) (L : Type w)
    [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [Algebra.IsAlgebraic K L] (k : K) (b : integralClosure R L) :
    integralClosureGenericFiberEquiv R K L (k ⊗ₜ[R] b) =
      algebraMap K L k * (b : L) := by
  simp only [integralClosureGenericFiberEquiv, Algebra.IsPushout.equiv_tmul]
  rfl

end SchemeTheory
