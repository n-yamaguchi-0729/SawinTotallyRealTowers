/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Associated
import Mathlib.RingTheory.Ideal.Height

/-!
# Height-one primes relative to one- and two-branch boundary equations

If a boundary equation is associated to a prime parameter, every height-one
prime either is that parameter divisor or lies on its complement.  If the
boundary is associated to a prime parameter times a power of a second prime
parameter, the only additional possibility is the second parameter divisor.

These statements use only the principal-prime geometry of a domain.  In
particular, they do not require a Noetherian hypothesis or any root-cover
presentation.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

private theorem heightOnePrime_eq_span_of_prime_mem
    {B : Type u} [CommRing B] [IsDomain B]
    {y : B} (hy : Prime y)
    (q : Ideal B) [q.IsPrime] (hqheight : q.height = 1)
    (hyq : y ∈ q) :
    q = Ideal.span {y} := by
  let branch : Ideal B := Ideal.span {y}
  let : branch.IsPrime := Ideal.isPrime_span_singleton_of_prime hy
  have hbranchLe : branch ≤ q := q.span_singleton_le_iff_mem.mpr hyq
  have hbranchNe : branch ≠ ⊥ := by
    simpa [branch, Ideal.span_singleton_eq_bot] using hy.ne_zero
  let : q.FiniteHeight :=
    Ideal.finiteHeight_iff_lt.mpr (Or.inr (by simp [hqheight]))
  let : branch.FiniteHeight :=
    Ideal.finiteHeight_of_le hbranchLe (inferInstance : q.IsPrime).ne_top
  have hqHeightLe : q.height ≤ branch.height := by
    rw [hqheight]
    exact Order.one_le_iff_ne_zero.mpr
      (Ideal.height_eq_zero_iff_eq_bot.not.mpr hbranchNe)
  exact (branch.eq_of_le_of_height_le hbranchLe hqHeightLe).symm

/-- If a boundary equation is associated to a prime parameter, a height-one
prime is either the corresponding parameter divisor or is disjoint from all
powers of the boundary equation. -/
theorem heightOnePrime_eq_span_or_disjoint_powers_of_associated
    {B : Type u} [CommRing B] [IsDomain B]
    {f y : B} (hy : Prime y) (hfy : Associated f y)
    (q : Ideal B) [q.IsPrime] (hqheight : q.height = 1) :
    q = Ideal.span {y} ∨
      Disjoint ((Submonoid.powers f : Submonoid B) : Set B) (q : Set B) := by
  by_cases hyq : y ∈ q
  · exact Or.inl (heightOnePrime_eq_span_of_prime_mem hy q hqheight hyq)
  · right
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact fun hfq ↦ hyq ((Ideal.mem_iff_of_associated hfy).mp hfq)

/-- If a boundary equation is associated to a prime parameter times a power
of a second prime parameter, a height-one prime is one of the two parameter
divisors or is disjoint from all powers of the boundary equation.

No positivity assumption on `n` is needed: for `n = 0` the statement reduces
to the one-branch case. -/
theorem heightOnePrime_eq_span_or_eq_span_or_disjoint_powers_of_associated_mul_pow
    {B : Type u} [CommRing B] [IsDomain B]
    {f y z : B} {n : ℕ}
    (hy : Prime y) (hz : Prime z) (hfy : Associated f (y * z ^ n))
    (q : Ideal B) [q.IsPrime] (hqheight : q.height = 1) :
    q = Ideal.span {y} ∨ q = Ideal.span {z} ∨
      Disjoint ((Submonoid.powers f : Submonoid B) : Set B) (q : Set B) := by
  by_cases hyq : y ∈ q
  · exact Or.inl (heightOnePrime_eq_span_of_prime_mem hy q hqheight hyq)
  · by_cases hzq : z ∈ q
    · exact Or.inr <| Or.inl
        (heightOnePrime_eq_span_of_prime_mem hz q hqheight hzq)
    · right
      right
      rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
      intro hfq
      have hprod : y * z ^ n ∈ q :=
        (Ideal.mem_iff_of_associated hfy).mp hfq
      rcases (inferInstance : q.IsPrime).mem_or_mem hprod with hyq' | hzpow
      · exact hyq hyq'
      · exact hzq ((inferInstance : q.IsPrime).mem_of_pow_mem n hzpow)

end EtaleFundamentalGroups

end
