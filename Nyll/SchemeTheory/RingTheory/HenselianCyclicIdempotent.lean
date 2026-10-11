/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.CyclicIdempotentAnnihilator
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.Ring

/-!
# Lifting a cyclic quotient idempotent over a Henselian pair

The determinant trick gives an annihilator reducing to `(X - 1) * X ^ d`.
Hensel's lemma lifts the simple root `1`. Dividing out this root and evaluating
the remaining factor constructs the desired idempotent in the finite algebra.
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

/-- A quotient idempotent whose factor is cyclic over the base lifts to an
idempotent in a finite algebra over a Henselian pair. -/
theorem exists_idempotent_lift_of_cyclic_quotient
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (I : Ideal R) [HenselianRing R I] (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b))
    (hcyc : ∀ x : B ⧸ I.map (algebraMap R B), ∃ r : R,
      Ideal.Quotient.mk (I.map (algebraMap R B)) b * x =
        r • Ideal.Quotient.mk (I.map (algebraMap R B)) b) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R B)) e =
        Ideal.Quotient.mk (I.map (algebraMap R B)) b := by
  let J : Ideal B := I.map (algebraMap R B)
  let qR : R →+* R ⧸ I := Ideal.Quotient.mk I
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  obtain ⟨d, hd, p, hpmonic, hproot, hpmap⟩ :=
    exists_monic_annihilator_of_cyclic_quotient_idempotent
      I (HenselianRing.jac (R := R) (I := I)) b hb hcyc
  have hpone : p.eval 1 ∈ I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← eval_one_map, hpmap, eval_mul, eval_sub, eval_X, eval_one,
      sub_self, zero_mul]
  have hpderiv : qR (p.derivative.eval 1) = 1 := by
    rw [← eval_one_map, ← derivative_map, hpmap, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_one, sub_zero,
      eval_add, eval_mul, eval_sub, eval_X, eval_one, eval_pow, one_pow,
      sub_self, zero_mul, add_zero, one_mul]
  obtain ⟨a, hpa, hai⟩ := HenselianRing.is_henselian
    (R := R) (I := I) p hpmonic 1 hpone (by rw [hpderiv]; exact isUnit_one)
  have haq : qR a = 1 := by
    have h : qR (a - 1) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hai
    simpa only [map_sub, map_one, sub_eq_zero] using h
  obtain ⟨q, hpq⟩ := (dvd_iff_isRoot (p := p) (a := a)).mpr hpa
  have hqmap : q.map qR = X ^ d := by
    have hregular : IsLeftRegular (X - (1 : (R ⧸ I)[X])) := by
      simpa only [C_1] using (monic_X_sub_C (1 : R ⧸ I)).isRegular.left
    apply hregular
    have h := congrArg (Polynomial.map qR) hpq
    rw [hpmap, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C, haq, C_1] at h
    exact h.symm
  have hcmap : qR (q.eval a) = 1 := by
    rw [← eval_map_apply, haq, hqmap, eval_pow, eval_X, one_pow]
  have hc : IsUnit (q.eval a) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    apply HenselianRing.jac (R := R) (I := I)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change qR (q.eval a - 1) = 0
    rw [map_sub, map_one, hcmap, sub_self]
  obtain ⟨z, hz⟩ := hc.exists_right_inv
  let t : B := aeval b q
  let c : B := algebraMap R B (q.eval a)
  let zB : B := algebraMap R B z
  have hbt : (b - algebraMap R B a) * t = 0 := by
    simpa only [hpq, aeval_mul, aeval_sub, aeval_X, aeval_C] using hproot
  obtain ⟨w, hw⟩ := (X_sub_C_dvd_sub_C_eval (p := q) (a := a))
  have htc : t - c = (b - algebraMap R B a) * aeval b w := by
    simpa only [aeval_sub, aeval_C, aeval_mul, aeval_X] using
      congrArg (aeval b) hw
  have ht : t * t = c * t := by
    apply sub_eq_zero.mp
    calc
      t * t - c * t = (t - c) * t := by ring
      _ = ((b - algebraMap R B a) * aeval b w) * t := by rw [htc]
      _ = ((b - algebraMap R B a) * t) * aeval b w := by ring
      _ = 0 := by rw [hbt, zero_mul]
  have hzB : c * zB = 1 := by
    change algebraMap R B (q.eval a) * algebraMap R B z = 1
    rw [← map_mul, hz, map_one]
  refine ⟨zB * t, ?_, ?_⟩
  · change (zB * t) * (zB * t) = zB * t
    calc
      (zB * t) * (zB * t) = (zB * zB) * (t * t) := by ring
      _ = (zB * zB) * (c * t) := by rw [ht]
      _ = (c * zB) * (zB * t) := by ring
      _ = zB * t := by rw [hzB, one_mul]
  · have hcomp : (algebraMap (R ⧸ I) (B ⧸ J)).comp qR =
        qB.comp (algebraMap R B) :=
      Ideal.quotientMap_comp_mk
        (show I ≤ J.comap (algebraMap R B) from Ideal.le_comap_map)
    have htq : qB t = qB b := by
      calc
        qB t = aeval (qB b) (q.map qR) :=
          Polynomial.map_aeval_eq_aeval_map hcomp q b
        _ = (qB b) ^ d := by rw [hqmap, map_pow, aeval_X]
        _ = qB b := hb.pow_eq (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hd))
    have hzbar : qR z = 1 := by
      have h := congrArg qR hz
      simpa only [map_mul, map_one, hcmap, one_mul] using h
    have hzBbar : qB zB = 1 := by
      calc
        qB zB = algebraMap (R ⧸ I) (B ⧸ J) (qR z) :=
          (RingHom.congr_fun hcomp z).symm
        _ = 1 := by rw [hzbar, map_one]
    change qB (zB * t) = qB b
    rw [map_mul, hzBbar, one_mul, htq]

end Algebra
