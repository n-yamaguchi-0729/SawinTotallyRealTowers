/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.Arithmetic
import Mathlib.Algebra.Order.Archimedean.Defs
import Mathlib.Data.Int.LeastGreatest
import Mathlib.Order.Filter.IsBounded
import Mathlib.Tactic.NormNum

/-!
# Lower bounds and a minimum for logarithm denominators

Linear growth dominates the logarithmic denominator contribution, so a single
integer lies strictly below every term of the resulting real sequence. The
corresponding integer sequence using `padicValNat` therefore attains a minimum.
-/

namespace LocalFieldTheory.DiscreteValuationField

/-- The logarithmic denominator estimate has an integer lower bound uniform in
the series index. This arithmetic statement does not require `p` to be prime. -/
theorem exists_int_lt_log_denominator_bound (p e : ℕ) :
    ∃ b : ℤ, ∀ n : ℕ,
      (b : ℝ) < ((n + 1 : ℕ) : ℝ) -
        (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) := by
  have ht : Filter.Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) -
        (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ))
      Filter.atTop Filter.atTop := by
    simpa only [mul_one] using
      (tendsto_nat_succ_mul_const_sub_const_mul_logb_atTop
        (p := p) (c := 1) (C := (e : ℝ)) zero_lt_one)
  obtain ⟨c, hc⟩ := Filter.bddBelow_range_of_tendsto_atTop_atTop ht
  obtain ⟨b, hb⟩ := exists_int_lt c
  exact ⟨b, fun n => hb.trans_le (hc (Set.mem_range_self n))⟩

/-- The exact integer denominator estimate attains a minimum at some series
index, with the lower bound constructed from logarithmic domination. -/
theorem exists_log_denominator_min (p e : ℕ) [Fact p.Prime] :
    ∃ m : ℕ, ∀ n : ℕ,
      ((m + 1 : ℕ) : ℤ) - (e : ℤ) * (padicValNat p (m + 1) : ℤ) ≤
        ((n + 1 : ℕ) : ℤ) - (e : ℤ) * (padicValNat p (n + 1) : ℤ) := by
  let f : ℕ → ℤ := fun n =>
    ((n + 1 : ℕ) : ℤ) - (e : ℤ) * (padicValNat p (n + 1) : ℤ)
  obtain ⟨b, hb⟩ := exists_int_lt_log_denominator_bound p e
  have hbound (n : ℕ) : b ≤ f n := by
    have hden : (e : ℝ) * (padicValNat p (n + 1) : ℝ) ≤
        (e : ℝ) * Real.logb (p : ℝ) ((n + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left (padicValNat_le_real_logb (p := p) (n + 1))
        (Nat.cast_nonneg e)
    have hreal : (b : ℝ) < ((n + 1 : ℕ) : ℝ) -
        (e : ℝ) * (padicValNat p (n + 1) : ℝ) :=
      (hb n).trans_le (sub_le_sub_left hden ((n + 1 : ℕ) : ℝ))
    change b ≤ ((n + 1 : ℕ) : ℤ) - (e : ℤ) * (padicValNat p (n + 1) : ℤ)
    exact_mod_cast hreal.le
  have hbounded : BddBelow (Set.range f) := by
    refine ⟨b, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hbound n
  obtain ⟨z, ⟨m, hm⟩, hz⟩ :=
    Int.exists_least_of_bdd (P := fun z => z ∈ Set.range f)
      (by
        obtain ⟨c, hc⟩ := hbounded
        exact ⟨c, fun z hz => hc hz⟩)
      ⟨f 0, Set.mem_range_self 0⟩
  refine ⟨m, ?_⟩
  intro n
  change f m ≤ f n
  rw [hm]
  exact hz (f n) (Set.mem_range_self n)

end LocalFieldTheory.DiscreteValuationField
