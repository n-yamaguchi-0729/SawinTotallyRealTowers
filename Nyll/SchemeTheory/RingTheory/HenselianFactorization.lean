/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianEtaleSection
public import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing

/-!
# Lifting coprime monic factorizations over Henselian pairs

The universal coprime factorization ring is étale over the coefficient ring.
Its section supplied by a factorization over the quotient therefore lifts over
a Henselian pair. Naturality of its representing equivalence gives the exact
reductions of both lifted factors.
-/

@[expose] public section

universe u

namespace Polynomial

/-- A monic coprime factorization over a quotient of a Henselian pair lifts to
a monic coprime factorization with the same fixed degrees and exact reductions.

The coefficient-based `MonicDegreeEq` type also handles trivial rings, so no
nontriviality assumption on the ring or its quotient is needed. -/
theorem exists_coprime_factorization_lift_of_henselian
    {R : Type u} [CommRing R] (I : Ideal R) [HenselianRing R I]
    {n : ℕ} (m k : ℕ) (hn : n = m + k) (p : MonicDegreeEq R n)
    (q₀ : MonicDegreeEq (R ⧸ I) m × MonicDegreeEq (R ⧸ I) k)
    (hprod : q₀.1.1 * q₀.2.1 = p.1.map (Ideal.Quotient.mk I))
    (hcoprime : IsCoprime q₀.1.1 q₀.2.1) :
    ∃ q : MonicDegreeEq R m × MonicDegreeEq R k,
      q.1.1 * q.2.1 = p.1 ∧ IsCoprime q.1.1 q.2.1 ∧
        q.1.map (Ideal.Quotient.mk I) = q₀.1 ∧
        q.2.map (Ideal.Quotient.mk I) = q₀.2 := by
  let U := UniversalCoprimeFactorizationRing m k hn p
  let σ : U →ₐ[R] R ⧸ I :=
    (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn p).symm
      ⟨q₀, hprod, hcoprime⟩
  obtain ⟨τ, hτ⟩ :=
    (Algebra.Etale.bijective_comp_quotient_of_henselian (B := U) I).2 σ
  let q := UniversalCoprimeFactorizationRing.homEquiv R m k hn p τ
  have hreduce :
      (UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn p
        ((Ideal.Quotient.mkₐ R I).comp τ)).1 = q₀ := by
    rw [hτ]
    exact congrArg Subtype.val
      ((UniversalCoprimeFactorizationRing.homEquiv (R ⧸ I) m k hn p).apply_symm_apply
        ⟨q₀, hprod, hcoprime⟩)
  have hfst : q.1.1.map (Ideal.Quotient.mk I) = q₀.1 :=
    (UniversalCoprimeFactorizationRing.homEquiv_comp_fst (S := R) m k hn p τ
      (Ideal.Quotient.mkₐ R I)).symm.trans (congrArg Prod.fst hreduce)
  have hsnd : q.1.2.map (Ideal.Quotient.mk I) = q₀.2 :=
    (UniversalCoprimeFactorizationRing.homEquiv_comp_snd (S := R) m k hn p τ
      (Ideal.Quotient.mkₐ R I)).symm.trans (congrArg Prod.snd hreduce)
  refine ⟨q.1, ?_, q.2.2, hfst, hsnd⟩
  simpa only [Algebra.algebraMap_self, Polynomial.map_id] using q.2.1

end Polynomial
