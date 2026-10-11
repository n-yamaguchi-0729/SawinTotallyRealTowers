/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic.Ring

/-!
# The reciprocal Eisenstein polynomial for an Artin--Schreier extension

The polynomial `X ^ n + C π * X ^ (n - 1) - C π` is Eisenstein at a prime
parameter `π` when `1 < n`. In an integrally closed domain it remains
irreducible over the fraction field. An inverse of any root satisfies
`α ^ n - α = π⁻¹`.

These algebraic sources need neither Henselianity nor a valuation. In the
intended DVR application, an irreducible uniformizer supplies the prime
parameter, and `n` is the residue characteristic. Galois and ramification
claims are not assumed here.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v w

section Polynomial

variable {R : Type u} [CommRing R]

/-- The polynomial of the inverse of a root of `X ^ n - X - π⁻¹`. -/
def artinSchreierInversePolynomial (π : R) (n : ℕ) : R[X] :=
  X ^ n + C π * X ^ (n - 1) - C π

private theorem artinSchreierInversePolynomial_natDegree_le
    (π : R) (n : ℕ) :
    (artinSchreierInversePolynomial π n).natDegree ≤ n := by
  refine (natDegree_sub_le (X ^ n + C π * X ^ (n - 1)) (C π)).trans ?_
  apply max_le
  · exact natDegree_add_le_of_degree_le (natDegree_X_pow_le n)
      ((natDegree_C_mul_X_pow_le π (n - 1)).trans (Nat.sub_le n 1))
  · rw [natDegree_C]
    exact Nat.zero_le n

private theorem artinSchreierInversePolynomial_coeff_top
    (π : R) (n : ℕ) (hn : 1 < n) :
    (artinSchreierInversePolynomial π n).coeff n = 1 := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)
  have hn1 : n ≠ n - 1 :=
    (Nat.sub_lt (lt_trans Nat.zero_lt_one hn) Nat.zero_lt_one).ne'
  simp only [artinSchreierInversePolynomial, coeff_sub, coeff_add,
    coeff_X_pow_self, coeff_C_mul_X_pow, ite_eq_right hn1, coeff_C,
    ite_eq_right hn0, add_zero, sub_zero]

/-- The reciprocal Artin--Schreier polynomial is monic. -/
theorem artinSchreierInversePolynomial_monic
    (π : R) (n : ℕ) (hn : 1 < n) :
    (artinSchreierInversePolynomial π n).Monic :=
  monic_of_natDegree_le_of_coeff_eq_one n
    (artinSchreierInversePolynomial_natDegree_le π n)
    (artinSchreierInversePolynomial_coeff_top π n hn)

/-- Its degree is the prescribed exponent. -/
theorem artinSchreierInversePolynomial_natDegree [Nontrivial R]
    (π : R) (n : ℕ) (hn : 1 < n) :
    (artinSchreierInversePolynomial π n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (artinSchreierInversePolynomial_natDegree_le π n)
    (by rw [artinSchreierInversePolynomial_coeff_top π n hn]; exact one_ne_zero)

private theorem artinSchreierInversePolynomial_coeff_zero
    (π : R) (n : ℕ) (hn : 1 < n) :
    (artinSchreierInversePolynomial π n).coeff 0 = -π := by
  have hn0 : 0 ≠ n := Nat.ne_of_lt (lt_trans Nat.zero_lt_one hn)
  have hn1 : 0 ≠ n - 1 := Nat.ne_of_lt (Nat.sub_pos_of_lt hn)
  simp only [artinSchreierInversePolynomial, coeff_sub, coeff_add,
    coeff_X_pow, ite_eq_right hn0, coeff_C_mul_X_pow, ite_eq_right hn1,
    coeff_C_zero, zero_add, zero_sub]

/-- A prime parameter makes the reciprocal polynomial Eisenstein. -/
theorem artinSchreierInversePolynomial_isEisensteinAt [IsDomain R]
    (π : R) (hπ : Prime π) (n : ℕ) (hn : 1 < n) :
    (artinSchreierInversePolynomial π n).IsEisensteinAt
      (Ideal.span ({π} : Set R)) := by
  have hP : (Ideal.span ({π} : Set R)).IsPrime :=
    (Ideal.span_singleton_prime hπ.ne_zero).mpr hπ
  refine (artinSchreierInversePolynomial_monic π n hn).isEisensteinAt_of_mem_of_notMem
    hP.ne_top ?_ ?_
  · intro i hi
    rw [artinSchreierInversePolynomial_natDegree π n hn] at hi
    rw [Ideal.mem_span_singleton]
    have h₁ : π ∣ (if i = n - 1 then π else 0) := by
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π
    have h₂ : π ∣ (if i = 0 then π else 0) := by
      split_ifs
      · exact dvd_rfl
      · exact dvd_zero π
    simpa only [artinSchreierInversePolynomial, coeff_sub, coeff_add,
      coeff_X_pow, ite_eq_right (Nat.ne_of_lt hi), zero_add,
      coeff_C_mul_X_pow, coeff_C] using dvd_sub h₁ h₂
  · rw [artinSchreierInversePolynomial_coeff_zero π n hn,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_neg]
    intro hdiv
    have hbad : 2 ≤ 1 :=
      (pow_dvd_pow_iff (a := π) (n := 2) (m := 1)
        hπ.ne_zero hπ.not_isUnit).mp (by simpa only [pow_one] using hdiv)
    exact (by decide : ¬ (2 ≤ 1)) hbad

/-- Eisenstein supplies irreducibility over the coefficient domain. -/
theorem artinSchreierInversePolynomial_irreducible [IsDomain R]
    (π : R) (hπ : Prime π) (n : ℕ) (hn : 1 < n) :
    Irreducible (artinSchreierInversePolynomial π n) := by
  apply (artinSchreierInversePolynomial_isEisensteinAt π hπ n hn).irreducible
    ((Ideal.span_singleton_prime hπ.ne_zero).mpr hπ)
    (artinSchreierInversePolynomial_monic π n hn).isPrimitive
  rw [artinSchreierInversePolynomial_natDegree π n hn]
  exact lt_trans Nat.zero_lt_one hn

/-- The same polynomial is irreducible in the fraction field. -/
theorem artinSchreierInversePolynomial_map_irreducible
    [IsDomain R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Prime π) (n : ℕ) (hn : 1 < n) :
    Irreducible ((artinSchreierInversePolynomial π n).map (algebraMap R K)) :=
  (artinSchreierInversePolynomial_monic π n hn).irreducible_iff_irreducible_map_fraction_map.mp
      (artinSchreierInversePolynomial_irreducible π hπ n hn)

end Polynomial

/-- Inverting an actual root gives the Artin--Schreier equation. The root
input is supplied, for example, by `AdjoinRoot.eval₂_root` applied to the
irreducible fraction-field polynomial above. -/
theorem artinSchreier_eq_of_inversePolynomial_root
    {K : Type v} {L : Type w} [Field K] [Field L] [Algebra K L]
    (π : K) (hπ : π ≠ 0) (n : ℕ) (hn : 1 < n)
    (β : L) (hβ : aeval β (artinSchreierInversePolynomial π n) = 0) :
    (β⁻¹) ^ n - β⁻¹ = algebraMap K L (π⁻¹) := by
  have hπL : algebraMap K L π ≠ 0 := by
    intro hzero
    apply hπ
    exact (algebraMap K L).injective
      (hzero.trans (map_zero (algebraMap K L)).symm)
  have hroot : β ^ n + algebraMap K L π * β ^ (n - 1) = algebraMap K L π := by
    apply sub_eq_zero.mp
    simpa only [artinSchreierInversePolynomial, map_sub, map_add,
      map_mul, map_pow, aeval_X, aeval_C] using hβ
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_trans Nat.zero_lt_one hn)
  have hn1 : n - 1 ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt hn)
  have hβ0 : β ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn0, zero_pow hn1, mul_zero, add_zero] at hroot
    exact hπL hroot.symm
  have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.le_of_lt hn)
  have hcancel : β ^ (n - 1) * (β⁻¹) ^ n = β⁻¹ := by
    calc
      β ^ (n - 1) * (β⁻¹) ^ n =
          β ^ (n - 1) * ((β⁻¹) ^ (n - 1) * β⁻¹) := by
        rw [← pow_succ, hpred]
      _ = β⁻¹ := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hβ0, one_pow, one_mul]
  have hlinear : 1 + algebraMap K L π * β⁻¹ =
      algebraMap K L π * (β⁻¹) ^ n := by
    calc
      1 + algebraMap K L π * β⁻¹ =
          (β ^ n + algebraMap K L π * β ^ (n - 1)) * (β⁻¹) ^ n := by
        rw [add_mul, ← mul_pow, mul_inv_cancel₀ hβ0, one_pow,
          mul_assoc, hcancel]
      _ = algebraMap K L π * (β⁻¹) ^ n := by rw [hroot]
  rw [map_inv₀, ← one_div (algebraMap K L π)]
  apply (eq_div_iff hπL).mpr
  calc
    ((β⁻¹) ^ n - β⁻¹) * algebraMap K L π =
        algebraMap K L π * (β⁻¹) ^ n - algebraMap K L π * β⁻¹ := by ring
    _ = 1 := by rw [← hlinear, add_sub_cancel_right]

end ValuationTheory.DiscreteValuationField
