/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Algebra.Group.Torsion
import Mathlib.Algebra.Module.End
import Mathlib.Tactic.Abel
/-!
# Odd prime order actions trivial modulo the prime

A binomial expansion shows that the augmentation image of such an action
on a torsion-free additive group is p-divisible. This does not require
finite generation or any topology on the group.
-/

namespace LocalFieldTheory.DiscreteValuationField

open scoped BigOperators

private theorem binomial_coefficient_three (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (j : ℕ) (hj : j < p - 1) :
    p ^ 3 ∣ p.choose (j + 2) * p ^ (j + 2) := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hjp : j + 2 ≤ p := by omega
  by_cases h : j + 2 = p
  · rw [h, Nat.choose_self, one_mul]
    exact Nat.pow_dvd_pow p hp3
  · have hd := Nat.mul_dvd_mul (hp.dvd_choose_self (by omega : j + 2 ≠ 0)
      (by omega : j + 2 < p)) (Nat.pow_dvd_pow p (by omega : 2 ≤ j + 2))
    simpa only [pow_succ', pow_two] using hd

private theorem binomial_prime_relation {R : Type*} [Ring R]
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (d : R)
    (hpow : (1 + p • d) ^ p = 1) :
    ∃ b : R, p ^ 2 • d = p ^ 3 • (d * b) := by
  let c (j : ℕ) : ℕ := (p.choose (j + 2) * p ^ (j + 2)) / p ^ 3
  let S : R := ∑ j ∈ Finset.range (p - 1), c j • d ^ (j + 1)
  have hc (j : ℕ) (hj : j ∈ Finset.range (p - 1)) :
      p.choose (j + 2) * p ^ (j + 2) = p ^ 3 * c j :=
    (Nat.mul_div_cancel' (binomial_coefficient_three p hp hp2 j
      (Finset.mem_range.mp hj))).symm
  have hterm (k : ℕ) :
      (p • d) ^ k * (1 : R) ^ (p - k) * (p.choose k : R) =
        (p.choose k * p ^ k) • d ^ k := by
    rw [one_pow, mul_one, smul_pow, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul]
    rw [mul_assoc, (Nat.cast_commute (p.choose k) (d ^ k)).eq.symm]
    rw [← mul_assoc, Nat.cast_comm]
  have hbin := (Commute.one_right (p • d)).add_pow p
  rw [add_comm (p • d) 1, hpow] at hbin
  simp only [hterm] at hbin
  have hcount : p + 1 = (p - 1 + 1) + 1 := by have := hp.two_le; omega
  rw [hcount, Finset.sum_range_succ', Finset.sum_range_succ'] at hbin
  simp only [Nat.zero_add, Nat.choose_one_right, pow_one, pow_zero,
    Nat.choose_zero_right, mul_one, one_smul] at hbin
  have hrest : (∑ j ∈ Finset.range (p - 1),
      (p.choose (j + 1 + 1) * p ^ (j + 1 + 1)) • d ^ (j + 1 + 1)) =
        p ^ 3 • (d * S) := by
    rw [show d * S = ∑ j ∈ Finset.range (p - 1), d * (c j • d ^ (j + 1)) from
      Finset.mul_sum .., nsmul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← nsmul_eq_mul, show j + 1 + 1 = j + 2 by omega, hc j hj, mul_smul]
    rw [mul_smul_comm, ← pow_succ', show j + 1 + 1 = j + 2 by omega]
  rw [hrest, ← pow_two p] at hbin
  refine ⟨-S, ?_⟩
  have hz : p ^ 3 • (d * S) + p ^ 2 • d = 0 := by
    exact add_right_cancel (hbin.symm.trans (zero_add (1 : R)).symm)
  rw [eq_neg_of_add_eq_zero_right hz, mul_neg, smul_neg]

/-- An automorphism of odd prime order congruent to the identity modulo that
prime has a prime-divisible augmentation image on every torsion-free group. -/
theorem primeOrder_action_sub_divisible
    {M : Type*} [AddCommGroup M] [IsAddTorsionFree M]
    (T : AddMonoid.End M) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hT : T ^ p = 1)
    (hdiv : ∀ x : M, ∃ y : M, T x - x = p • y) :
    ∀ x : M, ∃ y : M, T x - x = p • (T y - y) := by
  classical
  let d : AddMonoid.End M :=
    { toFun := fun x => Classical.choose (hdiv x)
      map_zero' := by
        apply nsmul_right_injective hp.ne_zero
        dsimp only
        rw [← Classical.choose_spec (hdiv 0), map_zero, sub_self, nsmul_zero]
      map_add' := fun x y => by
        apply nsmul_right_injective hp.ne_zero
        dsimp only
        rw [← Classical.choose_spec (hdiv (x + y)), nsmul_add,
          ← Classical.choose_spec (hdiv x), ← Classical.choose_spec (hdiv y), map_add]
        abel }
  have hd (x : M) : T x - x = p • d x := Classical.choose_spec (hdiv x)
  have hTd : T = 1 + p • d := by
    ext x
    change T x = x + p • d x
    rw [← hd x]
    abel
  obtain ⟨b, hb⟩ := binomial_prime_relation p hp hp2 d (hTd ▸ hT)
  have hdb (x : M) : d x = p • d (b x) := by
    have hx := congrArg (fun f : AddMonoid.End M => f x) hb
    change p ^ 2 • d x = p ^ 3 • d (b x) at hx
    rw [show p ^ 3 = p ^ 2 * p by ring, mul_smul] at hx
    exact nsmul_right_injective (pow_ne_zero 2 hp.ne_zero) hx
  intro x
  exact ⟨b x, by rw [hd, hdb x, hd]⟩

end LocalFieldTheory.DiscreteValuationField
