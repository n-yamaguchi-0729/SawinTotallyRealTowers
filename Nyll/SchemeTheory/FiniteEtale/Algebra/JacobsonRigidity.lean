/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Rigidity of unramified maps modulo the Jacobson radical

The separability element of an essentially finite type unramified algebra
annihilates the difference between two algebra maps. If the maps agree
modulo an ideal in the Jacobson radical, the image of that element is a
unit, forcing the maps to agree. This gives uniqueness for the morphism
lifting problem over a general henselian pair.
-/


@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.FormallyUnramified

variable {R : Type u} {A : Type v} {B : Type w}
  [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- Maps out of an essentially finite type unramified algebra are determined
by reduction modulo any ideal contained in the Jacobson radical. -/
theorem comp_injective_of_le_jacobson [FormallyUnramified R A] [EssFiniteType R A]
    (J : Ideal B) (hJ : J ≤ Ideal.jacobson ⊥) :
    Function.Injective
      ((Ideal.Quotient.mkₐ R J).comp : (A →ₐ[R] B) → A →ₐ[R] B ⧸ J) := by
  intro f g hfg
  obtain ⟨t, ht, htone⟩ :=
    (iff_exists_tensorProduct (R := R) (S := A)).mp inferInstance
  let q : B →ₐ[R] B ⧸ J := Ideal.Quotient.mkₐ R J
  let φ : A ⊗[R] A →ₐ[R] B :=
    Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)
  have hpoint (a : A) : q (f a) = q (g a) := AlgHom.congr_fun hfg a
  have hqφ : q.comp φ = (q.comp f).comp (Algebra.TensorProduct.lmul' R) := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, φ, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, map_mul]
    rw [hpoint b]
  have hqt : q (φ t) = 1 := by
    calc
      q (φ t) = q (f (Algebra.TensorProduct.lmul' R t)) := AlgHom.congr_fun hqφ t
      _ = 1 := by rw [htone, map_one, map_one]
  have hmem : φ t - 1 ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change q (φ t - 1) = 0
    rw [map_sub, hqt, map_one, sub_self]
  have hunit : IsUnit (φ t) :=
    Ideal.isUnit_of_sub_one_mem_jacobson_bot (φ t) (hJ hmem)
  apply AlgHom.ext
  intro a
  have hmul : (g a - f a) * φ t = 0 := by
    simpa only [map_mul, map_sub, map_zero, φ, Algebra.TensorProduct.lift_tmul,
      map_one, one_mul, mul_one] using congrArg φ (ht a)
  have hzero : g a - f a = 0 :=
    hunit.mul_right_cancel (hmul.trans (zero_mul (φ t)).symm)
  exact (sub_eq_zero.mp hzero).symm

end Algebra.FormallyUnramified
