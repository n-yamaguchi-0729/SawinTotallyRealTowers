/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.ConductorQuotient
import Nyll.SchemeTheory.PlaneCurves.Dimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Prime separation in a localized normalization

This file formalizes the weak-approximation argument in Fried--Jarden,
Lemma 6.3.2(b).  Pairwise distinct primes above a fixed maximal ideal are
separated by the Chinese remainder theorem.  The resulting elements are the
source of the lower bound on the dimension of the local normalization
quotient.

No finiteness of the normalization is used here.  Accordingly, the final
bound is first expressed through a linearly independent family (and hence
through `Module.rank`); the finite-dimensional `finrank` formulation follows
once Lemma 6.3.2(a), whose proof uses Lemma 6.3.1, is available.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace Lemma632

open Function

universe u v w

variable (K : Type u) (R : Type v) (S : Type w)
variable [Field K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra R S] [Algebra K S]
variable [IsScalarTower K R S] [Algebra.IsIntegral R S]

/-- The localization of the base ring at a prime ideal. -/
abbrev BaseLocalization (p : Ideal R) [p.IsPrime] :=
  Localization.AtPrime p

/--
The localization of the extension ring using the image of the complement of
`p`.  This is the ring denoted `S_p` in Fried--Jarden, Lemma 6.3.2.
-/
abbrev ExtensionLocalization (p : Ideal R) [p.IsPrime] :=
  Localization (Algebra.algebraMapSubmonoid S p.primeCompl)

section PrimeSeparation

variable {K R S}
variable {p : Ideal R} [p.IsMaximal]
variable {n : ℕ}

/-- The ideal of `S` underlying a chosen prime above `p`. -/
def extensionPrime (P : Fin (n + 1) ↪ p.primesOver S)
    (j : Fin (n + 1)) : Ideal S :=
  (P j).1

theorem extensionPrime_isMaximal
    (P : Fin (n + 1) ↪ p.primesOver S) (j : Fin (n + 1)) :
    (extensionPrime P j).IsMaximal :=
  Ideal.isMaximal_of_mem_primesOver (P j).property

/-- Distinct primes above a maximal ideal are pairwise coprime. -/
theorem extensionPrimes_pairwise_coprime
    (P : Fin (n + 1) ↪ p.primesOver S) :
    Pairwise (IsCoprime on extensionPrime P) := by
  intro i j hij
  let : (extensionPrime P i).IsMaximal :=
    extensionPrime_isMaximal P i
  let : (extensionPrime P j).IsMaximal :=
    extensionPrime_isMaximal P j
  apply Ideal.isCoprime_of_isMaximal
  intro hprime
  apply hij
  apply P.injective
  exact Subtype.ext hprime

/--
The Chinese-remainder element which is `1` at the `i`-th chosen prime and
`0` at every other chosen prime.
-/
def separatingElement
    (P : Fin (n + 1) ↪ p.primesOver S) (i : Fin n) : S :=
  (Ideal.exists_forall_sub_mem_ideal
    (extensionPrimes_pairwise_coprime P)
    (fun j : Fin (n + 1) => if j = i.castSucc then 1 else 0)).choose

theorem separatingElement_sub_one_mem
    (P : Fin (n + 1) ↪ p.primesOver S) (i : Fin n) :
    separatingElement P i - 1 ∈ extensionPrime P i.castSucc := by
  simpa [separatingElement] using
    (Ideal.exists_forall_sub_mem_ideal
      (extensionPrimes_pairwise_coprime P)
      (fun j : Fin (n + 1) => if j = i.castSucc then 1 else 0)).choose_spec
        i.castSucc

theorem separatingElement_mem
    (P : Fin (n + 1) ↪ p.primesOver S) (i : Fin n)
    (j : Fin (n + 1)) (hji : j ≠ i.castSucc) :
    separatingElement P i ∈ extensionPrime P j := by
  simpa [separatingElement, hji] using
    (Ideal.exists_forall_sub_mem_ideal
      (extensionPrimes_pairwise_coprime P)
      (fun j : Fin (n + 1) => if j = i.castSucc then 1 else 0)).choose_spec j

/-- Every separating element vanishes at the last chosen prime. -/
theorem separatingElement_mem_last
    (P : Fin (n + 1) ↪ p.primesOver S) (i : Fin n) :
    separatingElement P i ∈ extensionPrime P (Fin.last n) :=
  separatingElement_mem P i (Fin.last n) (by
    intro h
    have hval : n = i.val := congrArg Fin.val h
    omega)

end PrimeSeparation

end Lemma632
end Chapter06
end FieldArithmetic
