/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Field Arithmetic, Chapter 6: plane curves

This file starts the source-producing infrastructure for Section 6.1: scalar
extension to an algebraic closure and the zero sets of multivariate polynomials.
-/

namespace FieldArithmetic
namespace Chapter06

open MvPolynomial

universe u v

variable {K : Type u} [Field K]

/-- Extend the coefficients of a multivariate polynomial to an algebraic closure. -/
noncomputable def mapToAlgebraicClosure {σ : Type*} (f : MvPolynomial σ K) :
    MvPolynomial σ (AlgebraicClosure K) :=
  f.map (algebraMap K (AlgebraicClosure K))

/-- Absolute irreducibility, expressed over a fixed algebraic closure. -/
def IsAbsolutelyIrreducible {σ : Type*} (f : MvPolynomial σ K) : Prop :=
  Irreducible (mapToAlgebraicClosure f)

/--
An absolutely irreducible polynomial is already irreducible over its original
coefficient field.
-/
theorem IsAbsolutelyIrreducible.irreducible
    {σ : Type*} {f : MvPolynomial σ K}
    (hf : IsAbsolutelyIrreducible f) :
    Irreducible f := by
  let φ : K →+* AlgebraicClosure K :=
    algebraMap K (AlgebraicClosure K)
  have hφ : Function.Injective φ := RingHom.injective φ
  have reflectsUnits :
      ∀ g : MvPolynomial σ K,
        IsUnit (MvPolynomial.map φ g) → IsUnit g := by
    intro g hg
    rw [MvPolynomial.isUnit_iff_eq_C_of_isReduced] at hg ⊢
    obtain ⟨a, ha, hga⟩ := hg
    have hcoeff :
        φ (MvPolynomial.constantCoeff g) = a := by
      have := congrArg MvPolynomial.constantCoeff hga
      simpa using this
    refine ⟨MvPolynomial.constantCoeff g, ?_, ?_⟩
    · rw [isUnit_iff_ne_zero]
      intro hzero
      apply ha.ne_zero
      rw [← hcoeff, hzero, map_zero]
    · apply MvPolynomial.map_injective φ hφ
      rw [hga]
      simp [hcoeff]
  refine
    ⟨fun hunit =>
      hf.not_isUnit
        (IsUnit.map (MvPolynomial.map φ) hunit),
      fun a b hab => ?_⟩
  apply Or.imp (reflectsUnits a) (reflectsUnits b)
  apply hf.isUnit_or_isUnit
  change
    MvPolynomial.map φ f =
      MvPolynomial.map φ a * MvPolynomial.map φ b
  rw [hab, map_mul]

/-- The zero set of a multivariate polynomial after applying a coefficient map. -/
def affineZeroSet {σ : Type*} {R : Type u} {S : Type v}
    [CommSemiring R] [CommSemiring S] (φ : R →+* S) (f : MvPolynomial σ R) :
    Set (σ → S) :=
  {p | MvPolynomial.eval₂ φ p f = 0}

/-- The geometric zero set of a polynomial over a fixed algebraic closure. -/
noncomputable def geometricZeroSet {σ : Type*} (f : MvPolynomial σ K) :
    Set (σ → AlgebraicClosure K) :=
  affineZeroSet (algebraMap K (AlgebraicClosure K)) f

end Chapter06
end FieldArithmetic
