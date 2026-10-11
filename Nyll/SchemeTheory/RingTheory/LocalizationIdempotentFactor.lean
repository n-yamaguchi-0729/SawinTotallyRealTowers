/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.Ring

/-!
# Transporting an idempotent factor through a principal localization

If a map becomes bijective after inverting `b`, it identifies the factors on
which an idempotent is `1`, provided `b` is already a unit in the source factor.
The comparison is the actual map induced on the two quotient rings. In
particular, integrality of the source algebra passes to the target factor.
-/

@[expose] public section

universe u v w

namespace AlgHom

variable {R : Type u} {C : Type v} {B : Type w}
  [CommRing R] [CommRing C] [CommRing B] [Algebra R C] [Algebra R B]

/-- The map induced on the factors where `e` and `f e` become `1`.
The construction itself does not need idempotence. -/
  def idempotentFactorMap (f : C →ₐ[R] B) (e : C) :
    C ⧸ Ideal.span {1 - e} →ₐ[R] B ⧸ Ideal.span {1 - f e} :=
  Ideal.quotientMapₐ (Ideal.span {1 - f e}) f (by
    apply Ideal.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    change f (1 - e) ∈ Ideal.span {1 - f e}
    rw [map_sub, map_one]
    exact Ideal.mem_span_singleton_self (1 - f e))

@[simp]
theorem idempotentFactorMap_mk (f : C →ₐ[R] B) (e c : C) :
    f.idempotentFactorMap e (Ideal.Quotient.mk (Ideal.span {1 - e}) c) =
      Ideal.Quotient.mk (Ideal.span {1 - f e}) (f c) := rfl

/-- A bijective principal-localization map identifies an idempotent factor on
which the element being inverted is already a unit. -/
theorem bijective_idempotentFactorMap_of_awayMap_bijective
    (f : C →ₐ[R] B) (e : C) (he : IsIdempotentElem e) (b : C)
    (hb : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - e}) b))
    (hf : Function.Bijective (Localization.awayMap f.toRingHom b)) :
    Function.Bijective (f.idempotentFactorMap e) := by
  let qC : C →+* C ⧸ Ideal.span {1 - e} := Ideal.Quotient.mk _
  let qB : B →+* B ⧸ Ideal.span {1 - f e} := Ideal.Quotient.mk _
  let φ : C ⧸ Ideal.span {1 - e} →ₐ[R] B ⧸ Ideal.span {1 - f e} :=
    f.idempotentFactorMap e
  have hqe : qC e = 1 := by
    have h : qC (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (1 - e))
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h.symm
  have hinj := (Localization.awayMap_injective_iff (f := f.toRingHom) (r := b)).mp hf.1
  have hsurj := (Localization.awayMap_surjective_iff (f := f.toRingHom) (r := b)).mp hf.2
  constructor
  · have hzero (x : C ⧸ Ideal.span {1 - e}) (hx : φ x = 0) : x = 0 := by
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
      change qB (f c) = 0 at hx
      obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp
        (Ideal.Quotient.eq_zero_iff_mem.mp hx)
      have hefc : f (e * c) = 0 := by
        rw [map_mul, ht, ← mul_assoc, (he.map f).mul_one_sub_self, zero_mul]
      obtain ⟨n, hn⟩ := hinj (e * c) hefc
      have hn' : (qC b) ^ n * qC c = 0 := by
        simpa only [map_mul, map_pow, map_zero, hqe, one_mul] using congrArg qC hn
      apply (hb.pow n).mul_left_cancel
      rw [mul_zero]
      exact hn'
    intro x y hxy
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hxy, sub_self]
  · intro x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨c, n, hc⟩ := hsurj y
    obtain ⟨z, hz⟩ := (hb.pow n).exists_right_inv
    have hφqC (a : C) :
        φ (Ideal.Quotient.mk (Ideal.span {1 - e}) a) = qB (f a) := by
      rfl
    have hc' : φ (qC c) = (qB (f b)) ^ n * qB y := by
      change qB (f c) = (qB (f b)) ^ n * qB y
      change f c = f b ^ n * y at hc
      rw [hc, map_mul, map_pow]
    have hz' : (qB (f b)) ^ n * φ z = 1 := by
      calc
        (qB (f b)) ^ n * φ z =
            φ (Ideal.Quotient.mk (Ideal.span {1 - e}) b) ^ n * φ z := by
              rw [hφqC]
        _ = φ (Ideal.Quotient.mk (Ideal.span {1 - e}) b ^ n * z) := by
              rw [map_mul, map_pow]
        _ = φ 1 := congrArg φ hz
        _ = 1 := map_one φ
    refine ⟨qC c * z, ?_⟩
    change φ (qC c * z) = qB y
    rw [map_mul, hc']
    calc
      ((qB (f b)) ^ n * qB y) * φ z =
          ((qB (f b)) ^ n * φ z) * qB y := by ring
      _ = qB y := by rw [hz', one_mul]

/-- Under the same localization comparison, integrality of the source algebra
implies integrality of the target idempotent factor. -/
theorem isIntegral_idempotentFactor_of_awayMap_bijective
    [Algebra.IsIntegral R C] (f : C →ₐ[R] B)
    (e : C) (he : IsIdempotentElem e) (b : C)
    (hb : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - e}) b))
    (hf : Function.Bijective (Localization.awayMap f.toRingHom b)) :
    Algebra.IsIntegral R (B ⧸ Ideal.span {1 - f e}) := by
  let ψ : C →ₐ[R] B ⧸ Ideal.span {1 - f e} :=
    (Ideal.Quotient.mkₐ R (Ideal.span {1 - f e})).comp f
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := (f.bijective_idempotentFactorMap_of_awayMap_bijective e he b hb hf).2 y
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨c, hx⟩
  exact Algebra.IsIntegral.of_surjective ψ hψ

end AlgHom
