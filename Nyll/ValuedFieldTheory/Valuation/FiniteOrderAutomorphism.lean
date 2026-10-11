/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Ring.Aut
import Mathlib.Order.Monotone.Basic

/-!
# Finite-order automorphisms preserving a valuation class

An order-preserving permutation of a finite orbit cannot change the valuation
value at any point. Thus finite-order automorphisms preserving a valuation
class preserve the valuation itself.
-/

namespace Valuation
variable {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]

/-- A finite-order field automorphism preserving a valuation class preserves
its actual values, without any discreteness hypothesis. -/
theorem map_apply_eq_of_isEquiv_comap_of_pow_eq_one
    (v : Valuation K Γ) (τ : K ≃+* K)
    (hτ : v.IsEquiv (v.comap τ.toRingHom))
    (n : ℕ) (hn : 0 < n) (hpow : τ ^ n = 1) (x : K) : v (τ x) = v x := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep : ∀ k : ℕ, v ((τ ^ (k + 1)) x) < v ((τ ^ k) x) := by
      intro k
      induction k with
      | zero => simpa only [zero_add, pow_one, pow_zero, RingAut.one_apply] using hlt
      | succ k ih =>
        have h := hτ.lt_iff_lt.mp ih
        change v (τ ((τ ^ (k + 1)) x)) < v (τ ((τ ^ k) x)) at h
        simpa only [pow_succ', RingAut.mul_apply] using h
    have h := strictAnti_nat_of_succ_lt (f := fun k : ℕ => v ((τ ^ k) x)) hstep hn
    simp only [hpow, pow_zero, RingAut.one_apply, lt_self_iff_false] at h
  · have hstep : ∀ k : ℕ, v ((τ ^ k) x) < v ((τ ^ (k + 1)) x) := by
      intro k
      induction k with
      | zero => simpa only [zero_add, pow_one, pow_zero, RingAut.one_apply] using hgt
      | succ k ih =>
        have h := hτ.lt_iff_lt.mp ih
        change v (τ ((τ ^ k) x)) < v (τ ((τ ^ (k + 1)) x)) at h
        simpa only [pow_succ', RingAut.mul_apply] using h
    have h := strictMono_nat_of_lt_succ (f := fun k : ℕ => v ((τ ^ k) x)) hstep hn
    simp only [hpow, pow_zero, RingAut.one_apply, lt_self_iff_false] at h
end Valuation
