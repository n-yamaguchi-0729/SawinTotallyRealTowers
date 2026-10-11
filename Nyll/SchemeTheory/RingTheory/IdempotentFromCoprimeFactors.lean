/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Coprime.Basic
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.Ring

/-!
# Idempotents from coprime polynomial factors

A Bézout identity for two coprime factors of an annihilating polynomial gives
an idempotent after evaluation. If the factors reduce to positive powers of
`X - 1` and `X`, this idempotent lifts the given quotient idempotent.
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

/-- Coprime factors reducing to `(X - 1) ^ n` and `X ^ n` construct a lift
of a quotient idempotent by evaluating a Bézout identity. -/
theorem exists_idempotent_lift_of_coprime_polynomial_factors
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b))
    (n : ℕ) (hn : 1 ≤ n) (g h : R[X]) (hcoprime : IsCoprime g h)
    (hzero : aeval b (g * h) = 0)
    (hg : g.map (Ideal.Quotient.mk I) = (X - 1) ^ n)
    (hh : h.map (Ideal.Quotient.mk I) = X ^ n) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R B)) e =
        Ideal.Quotient.mk (I.map (algebraMap R B)) b := by
  let J : Ideal B := I.map (algebraMap R B)
  let qR : R →+* R ⧸ I := Ideal.Quotient.mk I
  let qB : B →+* B ⧸ J := Ideal.Quotient.mk J
  obtain ⟨s, t, hst⟩ := hcoprime
  let u : B := aeval b s
  let v : B := aeval b t
  let G : B := aeval b g
  let H : B := aeval b h
  have hbez : u * G + v * H = 1 := by
    simpa only [aeval_add, aeval_mul, aeval_one] using congrArg (aeval b) hst
  have hGH : G * H = 0 := by
    simpa only [aeval_mul] using hzero
  have hcompl : 1 - v * H = u * G := by
    rw [← hbez]
    ring
  refine ⟨v * H, ?_, ?_⟩
  · apply isIdempotentElem_iff_mul_one_sub_self.mpr
    calc
      (v * H) * (1 - v * H) = (v * H) * (u * G) := by rw [hcompl]
      _ = (u * v) * (G * H) := by ring
      _ = 0 := by rw [hGH, mul_zero]
  · have hcomp : (algebraMap (R ⧸ I) (B ⧸ J)).comp qR =
        qB.comp (algebraMap R B) :=
      Ideal.quotientMap_comp_mk
        (show I ≤ J.comap (algebraMap R B) from Ideal.le_comap_map)
    have hreduce (p : R[X]) : qB (aeval b p) = aeval (qB b) (p.map qR) :=
      Polynomial.map_aeval_eq_aeval_map hcomp p b
    have hGbar : qB G = (qB b - 1) ^ n := by
      change qB (aeval b g) = (qB b - 1) ^ n
      rw [hreduce, hg, map_pow, aeval_sub, aeval_X, aeval_one]
    have hHbar : qB H = qB b := by
      change qB (aeval b h) = qB b
      rw [hreduce, hh, map_pow, aeval_X]
      exact hb.pow_eq (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
    have hbG : qB b * qB G = 0 := by
      obtain ⟨m, hnm⟩ :=
        Nat.exists_eq_add_one_of_ne_zero (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))
      have hbsub : qB b * (qB b - 1) = 0 := by
        rw [mul_sub, mul_one, hb.eq, sub_self]
      rw [hGbar, hnm, pow_succ', ← mul_assoc, hbsub, zero_mul]
    have hbezbar : qB u * qB G + qB v * qB b = 1 := by
      simpa only [map_add, map_mul, map_one, hHbar] using congrArg qB hbez
    have hmul : qB u * (qB b * qB G) + qB v * (qB b * qB b) = qB b := by
      calc
        qB u * (qB b * qB G) + qB v * (qB b * qB b) =
            qB b * (qB u * qB G + qB v * qB b) := by ring
        _ = qB b := by rw [hbezbar, mul_one]
    rw [hbG, hb.eq, mul_zero, zero_add] at hmul
    change qB (v * H) = qB b
    rw [map_mul, hHbar]
    exact hmul

end Algebra
