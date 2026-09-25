/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum

set_option autoImplicit false

/-!
# Five generators for the permitted rational square classes

A squarefree integer supported on `3, 5, 7, 11, 13, 17` divides their
product. The primes `5, 13, 17` are one modulo four, while an even subset
of `3, 7, 11` contributes `1`, `21`, `33`, or `77`. The last contribution
is `21 * 33 / 3²`. This constructs an explicit rational square factor
and a product of a subset of the five radicands `5, 13, 17, 21, 33`.
-/

namespace ClassFieldTower.Sawin

/-- A squarefree natural number with the permitted prime support divides
the product of the six permitted primes. -/
theorem dvd_sixPrimeProduct_of_squarefree_support
    (n : ℕ) (hn : Squarefree n)
    (hSupport : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ ({3, 5, 7, 11, 13, 17} : Finset ℕ)) :
    n ∣ 255255 := by
  have hSubset : n.primeFactors ⊆ ({3, 5, 7, 11, 13, 17} : Finset ℕ) := by
    intro p hp
    exact hSupport p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hDiv := Finset.prod_dvd_prod_of_subset n.primeFactors
    ({3, 5, 7, 11, 13, 17} : Finset ℕ) id hSubset
  rw [show (∏ p ∈ n.primeFactors, id p) = n from Nat.prod_primeFactors_of_squarefree hn]
    at hDiv
  norm_num at hDiv
  exact hDiv

private theorem three_negative_primes_squareClass
    (s : Finset ℕ) (hs : s ⊆ {3, 7, 11}) (hMod : (∏ p ∈ s, p) % 4 = 1) :
    ∃ t : Finset ℕ, t ⊆ {21, 33} ∧
      ∃ q : ℚ, q ≠ 0 ∧ (∏ p ∈ s, (p : ℚ)) = (∏ r ∈ t, (r : ℚ)) * q ^ 2 := by
  have hChoices : s = ∅ ∨ s = {3, 7} ∨ s = {3, 11} ∨ s = {7, 11} := by
    have hMem := Finset.mem_powerset.mpr hs
    have hPower : ({3, 7, 11} : Finset ℕ).powerset =
        {∅, {3}, {7}, {11}, {3, 7}, {3, 11}, {7, 11}, {3, 7, 11}} := by decide
    rw [hPower] at hMem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · norm_num at hMod
    · norm_num at hMod
    · norm_num at hMod
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · norm_num at hMod
  rcases hChoices with rfl | rfl | rfl | rfl
  · exact ⟨∅, by decide, 1, by decide, by norm_num⟩
  · exact ⟨{21}, by decide, 1, by decide, by norm_num⟩
  · exact ⟨{33}, by decide, 1, by decide, by norm_num⟩
  · exact ⟨{21, 33}, by decide, 1 / 3, by norm_num, by norm_num⟩

/-- Every permitted squarefree radicand congruent to one modulo four is
a product of a subset of the five generators times an explicit nonzero
rational square. -/
theorem exists_five_generator_squareClass_of_support
    (n : ℕ) (hn : Squarefree n)
    (hSupport : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ ({3, 5, 7, 11, 13, 17} : Finset ℕ))
    (hMod : n % 4 = 1) :
    ∃ s : Finset ℕ, s ⊆ {5, 13, 17, 21, 33} ∧
      ∃ q : ℚ, q ≠ 0 ∧ (n : ℚ) = (∏ r ∈ s, (r : ℚ)) * q ^ 2 := by
  let good : Finset ℕ := n.primeFactors ∩ {5, 13, 17}
  let bad : Finset ℕ := n.primeFactors ∩ {3, 7, 11}
  have hGood : good ⊆ {5, 13, 17} := Finset.inter_subset_right
  have hBad : bad ⊆ {3, 7, 11} := Finset.inter_subset_right
  have hSubset : n.primeFactors ⊆ ({3, 5, 7, 11, 13, 17} : Finset ℕ) := by
    intro p hp
    exact hSupport p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hUnion : good ∪ bad = n.primeFactors := by
    dsimp only [good, bad]
    rw [← Finset.inter_union_distrib_left,
      show ({5, 13, 17} ∪ {3, 7, 11} : Finset ℕ) = {3, 5, 7, 11, 13, 17} by decide]
    exact Finset.inter_eq_left.mpr hSubset
  have hDisjoint : Disjoint good bad :=
    Finset.disjoint_of_subset_left hGood
      (Finset.disjoint_of_subset_right hBad (by decide))
  have hFactor : n = (∏ p ∈ good, p) * ∏ p ∈ bad, p := by
    rw [← Finset.prod_union hDisjoint, hUnion, Nat.prod_primeFactors_of_squarefree hn]
  have hGoodMod : (∏ p ∈ good, p) % 4 = 1 := by
    have h : Nat.ModEq 4 (∏ p ∈ good, p) 1 := Nat.ModEq.prod_one (by
      intro p hp
      have hpGood := hGood hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpGood
      rcases hpGood with rfl | rfl | rfl <;> decide)
    exact h
  have hBadMod : (∏ p ∈ bad, p) % 4 = 1 := by
    rw [hFactor, Nat.mul_mod, hGoodMod, one_mul, Nat.mod_mod] at hMod
    exact hMod
  obtain ⟨t, ht, q, hq, hClass⟩ := three_negative_primes_squareClass bad hBad hBadMod
  have hGoodT : Disjoint good t :=
    Finset.disjoint_of_subset_left hGood
      (Finset.disjoint_of_subset_right ht (by decide))
  refine ⟨good ∪ t,
    Finset.union_subset (hGood.trans (by decide)) (ht.trans (by decide)), q, hq, ?_⟩
  calc
    (n : ℚ) = (∏ p ∈ good, (p : ℚ)) * ∏ p ∈ bad, (p : ℚ) := by
      simpa only [Nat.cast_mul, Nat.cast_prod] using
        congrArg (fun m : ℕ ↦ (m : ℚ)) hFactor
    _ = (∏ r ∈ good ∪ t, (r : ℚ)) * q ^ 2 := by
      rw [hClass, Finset.prod_union hGoodT, mul_assoc]

/-- The square-class decomposition for a nonnegative integer radicand,
with the support expressed by divisibility in the integers. -/
theorem exists_five_generator_squareClass_of_int_support
    (d : ℤ) (hdNonneg : 0 ≤ d) (hd : Squarefree d.natAbs)
    (hSupport : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d →
      p ∈ ({3, 5, 7, 11, 13, 17} : Finset ℕ))
    (hMod : d % 4 = 1) :
    ∃ s : Finset ℕ, s ⊆ {5, 13, 17, 21, 33} ∧
      ∃ q : ℚ, q ≠ 0 ∧ (d : ℚ) = (∏ r ∈ s, (r : ℚ)) * q ^ 2 := by
  have hAbs : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hdNonneg
  have hNatMod : d.natAbs % 4 = 1 := by
    apply Int.natCast_inj.mp
    norm_num only [Int.natCast_mod, hAbs]
    exact hMod
  obtain ⟨s, hs, q, hq, hClass⟩ :=
    exists_five_generator_squareClass_of_support d.natAbs hd
      (fun p hp hDiv ↦ hSupport p hp (Int.natCast_dvd.mpr hDiv)) hNatMod
  have hRat : (d.natAbs : ℚ) = (d : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : ℚ)) hAbs
  rw [hRat] at hClass
  exact ⟨s, hs, q, hq, hClass⟩

end ClassFieldTower.Sawin
