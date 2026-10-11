/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-!
# Square classes in quadratic Galois extensions

The nontrivial automorphism has exactly the base field as its fixed field.
An anti-invariant generator gives the two base-field square classes which
become squares in the extension.
-/

namespace KummerTheory

universe u v

/-- An element fixed by the nonidentity quadratic automorphism lies in the base field. -/
theorem quadratic_aut_fixed_iff
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (hdim : Module.finrank K L = 2) (τ : Gal(L/K)) (hτ : τ ≠ 1) (z : L) :
    τ z = z ↔ ∃ x : K, algebraMap K L x = z := by
  have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  have hcard : Nat.card Gal(L/K) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hdim
  obtain ⟨υ, _, hυ⟩ := (Nat.card_eq_two_iff' (1 : Gal(L/K))).mp hcard
  constructor
  · intro hz
    apply (IsGalois.mem_range_algebraMap_iff_fixed (F := K) z).mpr
    intro σ
    by_cases hσ : σ = 1
    · rw [hσ]
      rfl
    · have heq : σ = τ := (hυ σ hσ).trans (hυ τ hτ).symm
      rw [heq]
      exact hz
  · rintro ⟨x, rfl⟩
    exact τ.commutes x

/-- Every automorphism of a quadratic Galois extension is an involution. -/
theorem quadratic_aut_apply_twice
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (hdim : Module.finrank K L = 2) (τ : Gal(L/K)) (z : L) :
    τ (τ z) = z := by
  have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (by rw [hdim]; decide)
  have hcard : Nat.card Gal(L/K) = 2 := (IsGalois.card_aut_eq_finrank K L).trans hdim
  have hpow : τ ^ 2 = 1 := by rw [← hcard]; exact pow_card_eq_one'
  have heval := congrArg (fun σ : Gal(L/K) => σ z) hpow
  exact heval

/-- In characteristic zero a nonidentity quadratic automorphism supplies a nonsquare radicand. -/
theorem exists_quadratic_antiInvariant
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [CharZero K] (hdim : Module.finrank K L = 2) (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ a : K, ∃ α : L, α ≠ 0 ∧ α ^ 2 = algebraMap K L a ∧
      τ α = -α ∧ ¬ IsSquare a := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨x, hx⟩ : ∃ x : L, τ x ≠ x := by
    by_contra hn
    apply hτ
    apply AlgEquiv.ext
    intro x
    exact not_not.mp (fun hx => hn ⟨x, hx⟩)
  let α : L := x - τ x
  have hα0 : α ≠ 0 := fun hz => hx (sub_eq_zero.mp hz).symm
  have hanti : τ α = -α := by
    dsimp only [α]
    rw [map_sub, quadratic_aut_apply_twice hdim]
    ring
  have hsqfix : τ (α ^ 2) = α ^ 2 := by
    rw [map_pow, hanti, neg_sq]
  obtain ⟨a, ha⟩ := (quadratic_aut_fixed_iff hdim τ hτ (α ^ 2)).mp hsqfix
  refine ⟨a, α, hα0, ha.symm, hanti, ?_⟩
  rintro ⟨b, hb⟩
  have heq : α ^ 2 = (algebraMap K L b) ^ 2 := by
    rw [← ha, hb, map_mul, pow_two]
  have hfixed : τ α = α := by
    rcases eq_or_eq_neg_of_sq_eq_sq α (algebraMap K L b) heq with hp | hn
    · rw [hp, τ.commutes]
    · rw [hn, map_neg, τ.commutes]
  have hneg : α = -α := hfixed.symm.trans hanti
  have hzero : (2 : L) * α = 0 := by linear_combination hneg
  exact hα0 ((mul_eq_zero.mp hzero).resolve_left (by norm_num))

/-- A base-field element becomes a square exactly in the trivial or defining square class. -/
theorem isSquare_algebraMap_iff_of_quadratic
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    (hdim : Module.finrank K L = 2) (τ : Gal(L/K)) (hτ : τ ≠ 1)
    (a : K) (α : L) (hα0 : α ≠ 0)
    (hαsq : α ^ 2 = algebraMap K L a) (hanti : τ α = -α) (c : K) :
    IsSquare (algebraMap K L c) ↔ IsSquare c ∨ IsSquare (c / a) := by
  constructor
  · rintro ⟨β, hβ⟩
    have hβsq : algebraMap K L c = β ^ 2 := by rw [hβ, pow_two]
    have hβτ : (τ β) ^ 2 = β ^ 2 := by
      rw [← map_pow, ← hβsq, τ.commutes]
    rcases eq_or_eq_neg_of_sq_eq_sq (τ β) β hβτ with hfixed | hneg
    · obtain ⟨b, hb⟩ := (quadratic_aut_fixed_iff hdim τ hτ β).mp hfixed
      left
      refine ⟨b, (algebraMap K L).injective ?_⟩
      rw [map_mul, hb]
      exact hβ
    · have hdivfixed : τ (β / α) = β / α := by
        rw [map_div₀, hneg, hanti, neg_div_neg_eq]
      obtain ⟨b, hb⟩ := (quadratic_aut_fixed_iff hdim τ hτ (β / α)).mp hdivfixed
      right
      refine ⟨b, (algebraMap K L).injective ?_⟩
      rw [map_div₀, hβsq, ← hαsq, map_mul, hb, ← div_pow, pow_two]
  · intro hc
    rcases hc with hc | hca
    · exact hc.map (algebraMap K L)
    · have ha0 : a ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hαsq
        exact (pow_ne_zero 2 hα0) hαsq
      have hsq : IsSquare (algebraMap K L a) := ⟨α, by rw [← hαsq, pow_two]⟩
      have hprod := hsq.mul (hca.map (algebraMap K L))
      rw [← map_mul, mul_div_cancel₀ c ha0] at hprod
      exact hprod

end KummerTheory
