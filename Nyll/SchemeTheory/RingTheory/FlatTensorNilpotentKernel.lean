/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Flat base change of a ring map with nilpotent kernel elements

Exactness of tensoring with a flat algebra represents every element killed
by base change using elements of the original kernel. Their images are
nilpotent, so the resulting finite sum is nilpotent as well.
-/

noncomputable section

open scoped TensorProduct

namespace SchemeTheory

universe u v w

/-- Flat base change preserves the condition that every kernel element is
nilpotent. No uniform nilpotence exponent is required. -/
theorem ker_includeLeft_le_nilradical_of_flat
    (R : Type u) (N : Type v) (T : Type w)
    [CommRing R] [CommRing N] [CommRing T]
    [Algebra R N] [Algebra R T] [Module.Flat R T]
    (hker : RingHom.ker (algebraMap R N) ≤ nilradical R) :
    RingHom.ker (algebraMap T (T ⊗[R] N)) ≤ nilradical T := by
  intro t ht
  let f : R →ₗ[R] N := Algebra.linearMap R N
  have hzero : f.lTensor T (t ⊗ₜ[R] (1 : R)) = 0 := by
    rw [LinearMap.lTensor_tmul]
    change t ⊗ₜ[R] algebraMap R N 1 = 0
    rw [map_one]
    exact ht
  obtain ⟨z, hz⟩ :=
    (Module.Flat.lTensor_exact T (LinearMap.exact_subtype_ker_map f)
      (t ⊗ₜ[R] (1 : R))).mp hzero
  let δ : T ⊗[R] LinearMap.ker f →ₗ[R] T :=
    (TensorProduct.rid R T).toLinearMap.comp ((LinearMap.ker f).subtype.lTensor T)
  have hδ : ∀ y : T ⊗[R] LinearMap.ker f, δ y ∈ nilradical T := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b r =>
      change (r : R) • b ∈ nilradical T
      rw [Algebra.smul_def]
      apply (nilradical T).mul_mem_right b
      exact mem_nilradical.mpr ((mem_nilradical.mp (hker r.property)).map
        (algebraMap R T))
    | add x y hx hy =>
      rw [map_add]
      exact (nilradical T).add_mem hx hy
  have hδz : δ z = t := by
    change (TensorProduct.rid R T) ((LinearMap.ker f).subtype.lTensor T z) = t
    rw [hz, TensorProduct.rid_tmul, one_smul]
  exact hδz ▸ hδ z

end SchemeTheory
