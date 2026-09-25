/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# A countable Frobenius relation budget

Depths n + 5 leave a strict negative Golod--Shafarevich margin at t = 5/12.
This numerical file does not assert that the required Frobenius elements
or their deep lifts have already been constructed.
-/

namespace ClassFieldTower.Sawin

/-- The depth required of the nth extra Frobenius relation. -/
def sawinFrobeniusDepth (n : ℕ) : ℕ := n + 5

/-- The geometric upper bound for the nth extra relation weight. -/
noncomputable def sawinFrobeniusCost (n : ℕ) : ℝ :=
  (5 / 12 : ℝ) ^ sawinFrobeniusDepth n

/-- The full countable cost is strictly smaller than the initial margin. -/
theorem sawinFrobeniusCost_hasSum :
    HasSum sawinFrobeniusCost (3125 / 145152 : ℝ) := by
  have h := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 5 / 12)
    (by norm_num : (5 / 12 : ℝ) < 1)).mul_right ((5 / 12 : ℝ) ^ 5)
  have hv : ((1 : ℝ) - 5 / 12)⁻¹ * (5 / 12) ^ 5 = 3125 / 145152 := by
    norm_num
  rw [hv] at h
  change HasSum (fun n : ℕ ↦ (5 / 12 : ℝ) ^ (n + 5)) _
  simpa only [pow_add] using h

theorem sawinFrobeniusCost_summable : Summable sawinFrobeniusCost :=
  sawinFrobeniusCost_hasSum.summable

theorem sawinFrobeniusCost_tsum :
    ∑' n : ℕ, sawinFrobeniusCost n = (3125 / 145152 : ℝ) :=
  sawinFrobeniusCost_hasSum.tsum_eq

theorem sawinFrobeniusCost_tsum_lt_margin :
    (∑' n : ℕ, sawinFrobeniusCost n) < (1 / 24 : ℝ) := by
  rw [sawinFrobeniusCost_tsum]
  norm_num

/-- Any greater depth consumes at most the scheduled geometric weight. -/
theorem sawinFrobeniusWeight_le_cost (depth : ℕ → ℕ)
    (hdepth : ∀ n : ℕ, sawinFrobeniusDepth n ≤ depth n) (n : ℕ) :
    (5 / 12 : ℝ) ^ depth n ≤ sawinFrobeniusCost n := by
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hdepth n)

theorem sawinFrobeniusWeight_summable (depth : ℕ → ℕ)
    (hdepth : ∀ n : ℕ, sawinFrobeniusDepth n ≤ depth n) :
    Summable (fun n : ℕ ↦ (5 / 12 : ℝ) ^ depth n) := by
  apply Summable.of_nonneg_of_le
    (fun n ↦ pow_nonneg (by norm_num) (depth n))
    (sawinFrobeniusWeight_le_cost depth hdepth)
    sawinFrobeniusCost_summable

theorem sawinFrobeniusWeight_tsum_le (depth : ℕ → ℕ)
    (hdepth : ∀ n : ℕ, sawinFrobeniusDepth n ≤ depth n) :
    (∑' n : ℕ, (5 / 12 : ℝ) ^ depth n) ≤ (3125 / 145152 : ℝ) := by
  rw [← sawinFrobeniusCost_tsum]
  exact (sawinFrobeniusWeight_summable depth hdepth).tsum_le_tsum
    (sawinFrobeniusWeight_le_cost depth hdepth) sawinFrobeniusCost_summable

/-- A relation rank at most six still leaves a strict negative margin
with all of the scheduled extra relations included. -/
theorem sawinGsPolynomial_with_frobenius_budget (r : ℕ) (hr : r ≤ 6)
    (depth : ℕ → ℕ)
    (hdepth : ∀ n : ℕ, sawinFrobeniusDepth n ≤ depth n) :
    (1 : ℝ) - 5 * (5 / 12) + r * (5 / 12) ^ 2 +
        (∑' n : ℕ, (5 / 12 : ℝ) ^ depth n) ≤ -2923 / 145152 := by
  have hrR : (r : ℝ) ≤ 6 := by exact_mod_cast hr
  have hsum := sawinFrobeniusWeight_tsum_le depth hdepth
  linarith

/-- Every finite selection of the scheduled relations obeys the same budget. -/
theorem sawinFrobeniusWeight_sum_le (depth : ℕ → ℕ)
    (hdepth : ∀ n : ℕ, sawinFrobeniusDepth n ≤ depth n) (s : Finset ℕ) :
    (∑ n ∈ s, (5 / 12 : ℝ) ^ depth n) ≤ (3125 / 145152 : ℝ) := by
  exact ((sawinFrobeniusWeight_summable depth hdepth).sum_le_tsum s
    (fun n _ ↦ pow_nonneg (by norm_num) (depth n))).trans
      (sawinFrobeniusWeight_tsum_le depth hdepth)

/-- The weighted polynomial stays strictly negative after any finite selection. -/
theorem sawinGsPolynomial_with_finite_frobenius_budget (r : ℕ) (hr : r ≤ 6)
    (depth : ℕ → ℕ)
    (hdepth : ∀ n : ℕ, sawinFrobeniusDepth n ≤ depth n) (s : Finset ℕ) :
    (1 : ℝ) - 5 * (5 / 12) + r * (5 / 12) ^ 2 +
        (∑ n ∈ s, (5 / 12 : ℝ) ^ depth n) ≤ -2923 / 145152 := by
  have hrR : (r : ℝ) ≤ 6 := by exact_mod_cast hr
  have hsum := sawinFrobeniusWeight_sum_le depth hdepth s
  linarith

/-- The exact finite-prefix inequality needed by the countable GS criterion. -/
theorem sawinGsPolynomial_frobenius_prefix_nonpos (r : ℕ) (hr : r ≤ 6) (N : ℕ) :
    (1 : ℝ) - 5 * (5 / 12) + (∑ _i : Fin r, (5 / 12 : ℝ) ^ 2) +
      (∑ i : Fin N, (5 / 12 : ℝ) ^ sawinFrobeniusDepth i) ≤ 0 := by
  have h := sawinGsPolynomial_with_finite_frobenius_budget r hr
    sawinFrobeniusDepth (fun _ ↦ le_rfl) (Finset.range N)
  have hneg : (-2923 / 145152 : ℝ) ≤ 0 := by norm_num
  have hle := h.trans hneg
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ ↦ (5 / 12 : ℝ) ^ sawinFrobeniusDepth n)]
  simpa using hle

end ClassFieldTower.Sawin
