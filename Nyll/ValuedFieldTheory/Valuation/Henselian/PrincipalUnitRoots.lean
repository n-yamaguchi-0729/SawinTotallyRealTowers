/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.NonmonicSimpleRoot
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Roots of principal units sufficiently close to one

In a Henselian valued field, every element closer to one than the square of
the value of a nonzero integer n is an nth power. Rescaling the binomial
polynomial gives a simple residual root, even when n is not a residue unit.
-/

namespace ValuationTheory

open Polynomial

private theorem exists_binomial_quadratic_remainder
    {R : Type*} [CommRing R] (n : ℕ) :
    ∃ Q : R[X], ∀ t : R, (1 + t) ^ n = 1 + (n : R) * t + t ^ 2 * Q.eval t := by
  have hdiv : (X : R[X]) ^ 2 ∣ (1 + X) ^ n - 1 - C (n : R) * X := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with rfl | rfl
    · simp only [coeff_sub, coeff_one_add_X_pow, Nat.choose_zero_right, Nat.cast_one,
        coeff_one_zero, coeff_C_mul, coeff_X_zero, mul_zero, sub_self]
    · simp only [coeff_sub, coeff_one_add_X_pow, Nat.choose_one_right, coeff_one,
        ite_eq_right (by decide : ¬ (1 : ℕ) = 0),
        coeff_C_mul, coeff_X_one, mul_one, sub_zero, sub_self]
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨Q, fun t => ?_⟩
  have ht := congrArg (fun f : R[X] => f.eval t) hQ
  simp only [eval_sub, eval_pow, eval_add, eval_one, eval_X, eval_mul, eval_C] at ht
  linear_combination ht

/-- The Hensel bound for nth roots near one, including the case when the
integer n is divisible by the residue characteristic. -/
theorem exists_pow_eq_of_valuation_sub_one_lt_natCast_sq
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (n : ℕ) (hn : (n : K) ≠ 0) (a : K)
    (ha : v (a - 1) < v (n : K) ^ 2) :
    ∃ b : K, b ^ n = a := by
  have hnpos : 0 < v (n : K) := (v.pos_iff).mpr hn
  have hcval : v ((1 - a) / (n : K) ^ 2) < 1 := by
    rw [v.map_div, map_pow, v.map_sub_swap]
    exact (div_lt_one₀ (pow_pos hnpos 2)).mpr ha
  let R := v.valuationSubring
  let c : R := ⟨(1 - a) / (n : K) ^ 2, hcval.le⟩
  obtain ⟨Q, hQ⟩ := exists_binomial_quadratic_remainder (R := R) n
  let f : R[X] := X + X ^ 2 * Q.comp (C (n : R) * X) + C c
  have hroot : f.eval 0 ∈ IsLocalRing.maximalIdeal R := by
    have hc : c ∈ IsLocalRing.maximalIdeal R := v.mem_maximalIdeal_iff.mpr hcval
    simpa only [f, eval_add, eval_X, eval_mul, eval_pow, zero_pow (by decide : 2 ≠ 0),
      zero_mul, zero_add, eval_C] using hc
  have hderiv : f.derivative.eval 0 = 1 := by
    simp only [f, derivative_add, derivative_X, derivative_mul, derivative_pow,
      derivative_C, eval_add, eval_one, eval_mul, eval_pow, eval_X, eval_C,
      show (2 - 1 : ℕ) = 1 by decide, pow_one, zero_mul, mul_zero, add_zero,
      zero_pow (by decide : 2 ≠ 0)]
  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
      (f.derivative.eval 0)) := by
    rw [hderiv, map_one]
    exact isUnit_one
  obtain ⟨z, hz, _⟩ :=
    DiscreteValuationField.exists_root_of_henselianRing_of_simpleRoot_mod
      v.valuationSubring f 0 hroot hunit
  have hzeval : z + z ^ 2 * Q.eval ((n : R) * z) + c = 0 := by
    simpa only [f, eval_add, eval_X, eval_mul, eval_pow, eval_comp, eval_C] using
      Polynomial.IsRoot.def.mp hz
  have hzK := congrArg ((↑) : R → K) hzeval
  change (z : K) + (z : K) ^ 2 * ((Q.eval ((n : R) * z) : R) : K) +
    (1 - a) / (n : K) ^ 2 = 0 at hzK
  have hexpand := congrArg ((↑) : R → K) (hQ ((n : R) * z))
  change (1 + (n : K) * (z : K)) ^ n =
    1 + (n : K) * ((n : K) * (z : K)) +
      ((n : K) * (z : K)) ^ 2 * ((Q.eval ((n : R) * z) : R) : K) at hexpand
  refine ⟨1 + (n : K) * (z : K), ?_⟩
  rw [hexpand]
  field_simp [hn] at hzK
  linear_combination hzK

/-- In a Henselian valued field, the nth-power subgroup of the multiplicative
group is open whenever n is nonzero in the field. -/
theorem isOpen_unit_pow_range
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
    [HenselianRing (Valued.v : Valuation K Γ).valuationSubring
      (IsLocalRing.maximalIdeal (Valued.v : Valuation K Γ).valuationSubring)]
    (n : ℕ) (hn : (n : K) ≠ 0) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  let v : Valuation K Γ := Valued.v
  have hn_nat : n ≠ 0 := by
    intro hzero
    exact hn (by rw [hzero, Nat.cast_zero])
  let U : Set Kˣ := {u | v.restrict ((u : K) - 1) < v.restrict (n : K) ^ 2}
  have hU : IsOpen U :=
    (Valued.isOpen_ball K (v.restrict (n : K) ^ 2)).preimage
      (Units.continuous_val.sub continuous_const)
  have hmem : (1 : Kˣ) ∈ U := by
    change v.restrict ((1 : K) - 1) < v.restrict (n : K) ^ 2
    rw [sub_self, map_zero]
    exact pow_pos (v.restrict.pos_iff.mpr hn) 2
  apply Subgroup.isOpen_of_mem_nhds (g := (1 : Kˣ))
  apply Filter.mem_of_superset (hU.mem_nhds hmem)
  intro u hu
  have hclose : v ((u : K) - 1) < v (n : K) ^ 2 := by
    change v.restrict ((u : K) - 1) < v.restrict (n : K) ^ 2 at hu
    rw [← map_pow] at hu
    simpa only [map_pow] using v.restrict_lt_iff.mp hu
  obtain ⟨b, hb⟩ := exists_pow_eq_of_valuation_sub_one_lt_natCast_sq v n hn (u : K) hclose
  have hb0 : b ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn_nat] at hb
    exact u.ne_zero hb.symm
  refine ⟨Units.mk0 b hb0, ?_⟩
  exact Units.ext hb

end ValuationTheory
