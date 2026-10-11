/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.HenselianFactorization
public import Nyll.SchemeTheory.RingTheory.IdempotentAnnihilator
public import Nyll.SchemeTheory.RingTheory.IdempotentFromCoprimeFactors
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.Tactic.Ring

/-!
# Lifting arbitrary quotient idempotents in finite algebras

A doubled generating family gives an annihilator reducing to powers of
`X - 1` and `X`. The Henselian factorization theorem lifts these coprime
factors, and evaluation of a Bézout identity gives the required idempotent.
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

/-- Every quotient idempotent of a finite algebra over a Henselian pair lifts
to an idempotent of the original algebra. -/
theorem exists_idempotent_lift_of_finite
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (I : Ideal R) [HenselianRing R I] (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b)) :
    ∃ e : B, IsIdempotentElem e ∧
      Ideal.Quotient.mk (I.map (algebraMap R B)) e =
        Ideal.Quotient.mk (I.map (algebraMap R B)) b := by
  cases subsingleton_or_nontrivial (R ⧸ I) with
  | inl h =>
    let : Subsingleton (R ⧸ I) := h
    let : Subsingleton (B ⧸ I.map (algebraMap R B)) :=
      Module.subsingleton (R ⧸ I) (B ⧸ I.map (algebraMap R B))
    exact ⟨0, by change (0 : B) * 0 = 0; exact zero_mul 0, Subsingleton.elim _ _⟩
  | inr h =>
    let : Nontrivial (R ⧸ I) := h
    obtain ⟨n, hn, p, hp, hpb, hpmap⟩ :=
      exists_monic_annihilator_of_quotient_idempotent I b hb
    have hm₁ : ((X - 1) ^ n : (R ⧸ I)[X]).Monic := by
      simpa only [C_1] using (monic_X_sub_C (1 : R ⧸ I)).pow n
    have hm₂ : (X ^ n : (R ⧸ I)[X]).Monic := monic_X.pow n
    have hd₁ : ((X - 1) ^ n : (R ⧸ I)[X]).natDegree = n := by
      have hdeg : ((X - C (1 : R ⧸ I)) ^ n).natDegree = n := by
        rw [(monic_X_sub_C (1 : R ⧸ I)).natDegree_pow, natDegree_X_sub_C, mul_one]
      simpa only [C_1] using hdeg
    have hd₂ : (X ^ n : (R ⧸ I)[X]).natDegree = n := by rw [natDegree_X_pow]
    have hpdeg : p.natDegree = n + n := by
      rw [← hp.natDegree_map (Ideal.Quotient.mk I), hpmap,
        hm₁.natDegree_mul hm₂, hd₁, hd₂]
    let P : MonicDegreeEq R (n + n) := MonicDegreeEq.mk p hp hpdeg
    let q₀ : MonicDegreeEq (R ⧸ I) n × MonicDegreeEq (R ⧸ I) n :=
      ⟨MonicDegreeEq.mk ((X - 1) ^ n) hm₁ hd₁, MonicDegreeEq.mk (X ^ n) hm₂ hd₂⟩
    have hcoprime : IsCoprime ((X - 1) ^ n : (R ⧸ I)[X]) (X ^ n) := by
      have hbase : IsCoprime (X - 1 : (R ⧸ I)[X]) X := ⟨-1, 1, by ring⟩
      exact hbase.pow
    obtain ⟨q, hprod, hcop, hq₁, hq₂⟩ :=
      Polynomial.exists_coprime_factorization_lift_of_henselian I n n rfl P q₀
        hpmap.symm hcoprime
    apply exists_idempotent_lift_of_coprime_polynomial_factors I b hb n hn
      q.1.1 q.2.1 hcop
    · rw [hprod]
      exact hpb
    · exact congrArg Subtype.val hq₁
    · exact congrArg Subtype.val hq₂

end Algebra
