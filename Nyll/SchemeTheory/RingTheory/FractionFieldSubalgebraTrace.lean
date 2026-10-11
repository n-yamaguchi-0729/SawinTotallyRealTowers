/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Trace.Basic

/-!
# Traces after localizing a subalgebra of a fraction field

For any subalgebra B of the fraction field K of a domain R, the actual
multiplication map K tensor B to K is an isomorphism. Flatness preserves the
inclusion B to K, and each element of K is the image of k tensor 1.
Consequently the trace of multiplication by b after base change is b itself.
The result does not assume that R is integrally closed.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace SchemeTheory

universe u v

variable (R : Type u) [CommRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

private def fractionFieldTensorSubalgebraHom (B : Subalgebra R K) :
    K ⊗[R] B →ₐ[K] K :=
  (AlgHom.liftEquiv R K B K) B.val

private theorem fractionFieldTensorSubalgebraHom_bijective (B : Subalgebra R K) :
    Function.Bijective (fractionFieldTensorSubalgebraHom R K B) := by
  let : Module.Flat R K := IsLocalization.flat K (nonZeroDivisors R)
  let e : K ⊗[R] K ≃ₐ[K] K := IsLocalization.algebraLid (nonZeroDivisors R) K K
  have hcomp (a : K ⊗[R] B) :
      e (B.val.toLinearMap.lTensor K a) = fractionFieldTensorSubalgebraHom R K B a := by
    induction a using TensorProduct.inductionOn with
    | tmul k b => rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  constructor
  · intro a b hab
    apply Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      B.val.toLinearMap Subtype.val_injective
    apply e.injective
    exact (hcomp a).trans (hab.trans (hcomp b).symm)
  · intro k
    refine ⟨k ⊗ₜ[R] (1 : B), ?_⟩
    change k * ((1 : B) : K) = k
    exact mul_one k

/-- Multiplication identifies the base change of any fraction-field
subalgebra with that fraction field. -/
def fractionFieldTensorSubalgebraEquiv (B : Subalgebra R K) :
    K ⊗[R] B ≃ₐ[K] K :=
  AlgEquiv.ofBijective (fractionFieldTensorSubalgebraHom R K B)
    (fractionFieldTensorSubalgebraHom_bijective R K B)

/-- The comparison is the actual multiplication map on pure tensors. -/
@[simp]
theorem fractionFieldTensorSubalgebraEquiv_tmul
    (B : Subalgebra R K) (k : K) (b : B) :
    fractionFieldTensorSubalgebraEquiv R K B (k ⊗ₜ[R] b) = k * (b : K) := rfl

/-- Multiplication by an element of a fraction-field subalgebra has that
same element as its trace after base change to the fraction field. -/
theorem trace_baseChange_lmul_subalgebra (B : Subalgebra R K) (b : B) :
    LinearMap.trace K (K ⊗[R] B) ((Algebra.lmul R B b).baseChange K) = (b : K) := by
  rw [Algebra.baseChange_lmul]
  change Algebra.trace K (K ⊗[R] B) (1 ⊗ₜ[R] b) = (b : K)
  rw [← Algebra.trace_eq_of_algEquiv (fractionFieldTensorSubalgebraEquiv R K B),
    fractionFieldTensorSubalgebraEquiv_tmul, one_mul, Algebra.trace_self_apply]

end SchemeTheory
