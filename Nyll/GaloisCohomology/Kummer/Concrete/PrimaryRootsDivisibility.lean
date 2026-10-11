/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Divisibility of an infinite primary group of roots of unity

An infinite primary subgroup in the units of a field contains primitive roots
of every prime-power order. Its power maps are surjective. Consequently, if the
only unit divisible by every positive integer is one, every primary root group
is finite. No assumption on characteristic is needed.
-/

namespace KummerTheory
universe u
variable {K : Type u} [Field K]

/-- An infinite primary group contains roots of every prime-power order. -/
theorem exists_primitiveRoot_prime_pow_of_infinite_primary
    (p : ℕ) [Fact p.Prime] [Infinite (CommGroup.primaryComponent Kˣ p)] (n : ℕ) :
    ∃ ζ : Kˣ, IsPrimitiveRoot ζ (p ^ n) := by
  classical
  have hp : p.Prime := Fact.out
  have hunbounded : ∃ z : CommGroup.primaryComponent Kˣ p, (z : Kˣ) ^ (p ^ n) ≠ 1 := by
    by_contra h
    push Not at h
    let : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
    let f : CommGroup.primaryComponent Kˣ p → rootsOfUnity (p ^ n) K :=
      fun z => ⟨z.1, (mem_rootsOfUnity _ _).2 (h z)⟩
    have hf : Function.Injective f := fun x y hxy =>
      Subtype.ext (congrArg (fun z : rootsOfUnity (p ^ n) K => (z : Kˣ)) hxy)
    have : Finite (CommGroup.primaryComponent Kˣ p) := Finite.of_injective f hf
    exact not_finite (CommGroup.primaryComponent Kˣ p)
  obtain ⟨z, hz⟩ := hunbounded
  obtain ⟨m, hm⟩ := CommGroup.mem_primaryComponent_iff_orderOf.mp z.property
  have hmn : n ≤ m := by
    by_contra h
    apply hz
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hm]
    exact pow_dvd_pow p (by omega)
  have hprim : IsPrimitiveRoot (z : Kˣ) (p ^ m) := IsPrimitiveRoot.iff_orderOf.mpr hm
  refine ⟨(z : Kˣ) ^ (p ^ (m - n)), ?_⟩
  exact hprim.pow (pow_pos hp.pos m)
    (by rw [← pow_add, Nat.sub_add_cancel hmn])

/-- Every prime-exponent power map is onto the infinite primary root group. -/
theorem primaryComponent_prime_pow_surjective_of_infinite
    (p : ℕ) [Fact p.Prime] [Infinite (CommGroup.primaryComponent Kˣ p)]
    (q : ℕ) (hq : q.Prime) :
    Function.Surjective (fun z : CommGroup.primaryComponent Kˣ p => z ^ q) := by
  intro z
  have hp : p.Prime := Fact.out
  obtain ⟨m, hm⟩ := CommGroup.mem_primaryComponent_iff_orderOf.mp z.property
  by_cases hqp : q = p
  · subst q
    obtain ⟨η, hη⟩ := exists_primitiveRoot_prime_pow_of_infinite_primary (K := K) p (m + 1)
    have hηp : IsPrimitiveRoot (η ^ p) (p ^ m) :=
      hη.pow (pow_pos hp.pos (m + 1)) (by rw [pow_succ, mul_comm])
    have hzpow : (z : Kˣ) ^ (p ^ m) = 1 := by rw [← hm, pow_orderOf_eq_one]
    let : NeZero (p ^ m) := ⟨pow_ne_zero m hp.ne_zero⟩
    obtain ⟨i, _, hi⟩ := hηp.eq_pow_of_mem_rootsOfUnity
      ((mem_rootsOfUnity (p ^ m) (z : Kˣ)).mpr hzpow)
    have hηmem : η ∈ CommGroup.primaryComponent Kˣ p := ⟨m + 1, hη.pow_eq_one⟩
    refine ⟨⟨η ^ i, (CommGroup.primaryComponent Kˣ p).pow_mem hηmem i⟩, ?_⟩
    apply Subtype.ext
    change (η ^ i) ^ p = (z : Kˣ)
    rw [pow_right_comm]
    exact hi
  · have hcop : q.Coprime (orderOf z) := by
      have hm' : orderOf z = p ^ m := by simpa only [orderOf_submonoid] using hm
      rw [hm']
      exact ((hq.coprime_iff_not_dvd).mpr
        (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))).pow_right m
    obtain ⟨i, hi⟩ := exists_pow_eq_self_of_coprime (x := z) hcop
    refine ⟨z ^ i, ?_⟩
    change (z ^ i) ^ q = z
    rw [pow_right_comm]
    exact hi

/-- Every positive power map is onto the infinite primary root group. -/
theorem primaryComponent_pow_surjective_of_infinite
    (p : ℕ) [Fact p.Prime] [Infinite (CommGroup.primaryComponent Kˣ p)]
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective (fun z : CommGroup.primaryComponent Kˣ p => z ^ n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn1 : n = 1
    · subst n
      intro z
      exact ⟨z, pow_one z⟩
    obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
    have hdivpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn) hq.pos
    have hdivlt : n / q < n := Nat.div_lt_self hn hq.one_lt
    intro z
    obtain ⟨y, hy⟩ := ih (n / q) hdivlt hdivpos z
    obtain ⟨x, hx⟩ := primaryComponent_prime_pow_surjective_of_infinite p q hq y
    refine ⟨x, ?_⟩
    change x ^ n = z
    rw [← Nat.mul_div_cancel' hqn, pow_mul]
    exact (congrArg (fun a => a ^ (n / q)) hx).trans hy

/-- Absence of nontrivial infinitely divisible units bounds each primary group. -/
theorem finite_primaryComponent_of_no_infinitely_divisible_units
    (hK : ∀ z : Kˣ, (∀ n : ℕ, 0 < n → ∃ y : Kˣ, y ^ n = z) → z = 1)
    (p : ℕ) [Fact p.Prime] :
    Finite (CommGroup.primaryComponent Kˣ p) := by
  classical
  by_contra hfinite
  have : Infinite (CommGroup.primaryComponent Kˣ p) := not_finite_iff_infinite.mp hfinite
  have hsub : Subsingleton (CommGroup.primaryComponent Kˣ p) := by
    apply subsingleton_of_forall_eq 1
    intro z
    apply Subtype.ext
    change (z : Kˣ) = 1
    apply hK
    intro n hn
    obtain ⟨y, hy⟩ := primaryComponent_pow_surjective_of_infinite p n hn z
    exact ⟨y.1, congrArg Subtype.val hy⟩
  have : Finite (CommGroup.primaryComponent Kˣ p) := inferInstance
  exact not_finite (CommGroup.primaryComponent Kˣ p)

end KummerTheory
