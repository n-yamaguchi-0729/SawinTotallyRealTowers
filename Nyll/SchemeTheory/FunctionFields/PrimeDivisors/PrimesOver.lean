/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Counting primes above a prime ideal

The fundamental equality between ramification indices, inertia degrees, and
the rank of a finite flat extension immediately bounds the number of primes
above a fixed prime.  This file records that consequence in a form convenient
for the prime-divisor counts in Fried--Jarden, Lemma 6.2.2.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace PrimeCounting

universe u v

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/--
The number of primes of a finite flat algebra above a prime ideal is at most
the rank of the algebra.

This is slightly stronger than the Dedekind-domain version needed for function
fields: every ramification-index/inertia-degree summand is positive, so the
number of summands is bounded by their sum.
-/
theorem card_primesOver_le_finrank
    [IsDomain R] [Module.Finite R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] :
    Nat.card (p.primesOver S) ≤ Module.finrank R S := by
  classical
  let : Fintype (p.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) p).fintype
  rw [← p.sum_ramification_inertia_eq_finrank S, Nat.card_eq_fintype_card]
  calc
    Fintype.card (p.primesOver S) = ∑ _q : p.primesOver S, 1 := by simp
    _ ≤ ∑ q : p.primesOver S, q.1.ramificationIdx R * q.1.inertiaDeg R := by
      exact Finset.sum_le_sum fun q (_ : q ∈ Finset.univ) ↦
        Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (q.1.ramificationIdx_pos R).ne'
            (q.1.inertiaDeg_pos R).ne')

/--
Dedekind-domain specialization: a finite torsion-free algebra is flat, hence
the number of primes above any prime ideal is bounded by its module rank.
-/
theorem card_primesOver_le_finrank_of_isDedekindDomain
    [IsDedekindDomain R] [Module.IsTorsionFree R S] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime] :
    Nat.card (p.primesOver S) ≤ Module.finrank R S :=
  card_primesOver_le_finrank p

end PrimeCounting
end Chapter06
end FieldArithmetic
