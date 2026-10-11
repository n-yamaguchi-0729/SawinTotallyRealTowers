/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteCharacterAction
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteConjugation
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The action on continuous absolute Galois characters

Inverse semilinear conjugation preserves continuity. Restricting the algebraic
character action therefore gives the action on continuous abelian characters.
-/

namespace KummerTheory

variable {K A : Type*} [Field K] [CommGroup A] [TopologicalSpace A]

/-- Pullback by inverse conjugation preserves continuous characters. -/
noncomputable def absoluteContinuousCharacterTransform (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →ₜ* A) : Gal(AlgebraicClosure K/K) →ₜ* A :=
  ⟨absoluteGaloisCharacterTransform τ f.toMonoidHom,
    f.continuous.comp (absoluteGaloisConjugateEquiv_continuous τ.symm)⟩

/-- The continuous transform has the same pointwise formula as the algebraic one. -/
theorem absoluteContinuousCharacterTransform_apply (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →ₜ* A) (σ : Gal(AlgebraicClosure K/K)) :
    absoluteContinuousCharacterTransform τ f σ =
      f (absoluteGaloisConjugate τ.symm σ) := by
  rfl

/-- Identity on continuous characters follows from independence of the lift. -/
theorem absoluteContinuousCharacterTransform_one
    (f : Gal(AlgebraicClosure K/K) →ₜ* A) :
    absoluteContinuousCharacterTransform 1 f = f := by
  apply ContinuousMonoidHom.ext
  intro σ
  exact DFunLike.congr_fun (absoluteGaloisCharacterTransform_one f.toMonoidHom) σ

/-- The continuous transforms satisfy the left action composition law. -/
theorem absoluteContinuousCharacterTransform_mul (τ υ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →ₜ* A) :
    absoluteContinuousCharacterTransform (τ * υ) f =
      absoluteContinuousCharacterTransform τ (absoluteContinuousCharacterTransform υ f) := by
  apply ContinuousMonoidHom.ext
  intro σ
  exact DFunLike.congr_fun (absoluteGaloisCharacterTransform_mul τ υ f.toMonoidHom) σ

variable [IsTopologicalGroup A]

/-- The base automorphism group acts on continuous abelian Galois characters. -/
noncomputable def absoluteContinuousCharacterAction :
    RingAut K →* MulAut (Gal(AlgebraicClosure K/K) →ₜ* A) where
  toFun τ :=
    { toFun := absoluteContinuousCharacterTransform τ
      invFun := absoluteContinuousCharacterTransform τ⁻¹
      left_inv f := by
        rw [← absoluteContinuousCharacterTransform_mul, inv_mul_cancel,
          absoluteContinuousCharacterTransform_one]
      right_inv f := by
        rw [← absoluteContinuousCharacterTransform_mul, mul_inv_cancel,
          absoluteContinuousCharacterTransform_one]
      map_mul' f g := by
        apply ContinuousMonoidHom.ext
        intro σ
        rfl }
  map_one' := by
    apply MulEquiv.ext
    intro f
    exact absoluteContinuousCharacterTransform_one f
  map_mul' τ υ := by
    apply MulEquiv.ext
    intro f
    exact absoluteContinuousCharacterTransform_mul τ υ f

/-- Evaluation of the action by a base automorphism. -/
theorem absoluteContinuousCharacterAction_apply (τ : RingAut K)
    (f : Gal(AlgebraicClosure K/K) →ₜ* A) :
    absoluteContinuousCharacterAction τ f = absoluteContinuousCharacterTransform τ f := by
  rfl

end KummerTheory
