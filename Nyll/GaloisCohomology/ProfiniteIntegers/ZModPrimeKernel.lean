/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.ZMod.Basic

/-!
# The prime-order kernel of successive prime-power reduction
-/

namespace ZMod

/-- Multiplication by p^n identifies residues modulo p with the last kernel layer. -/
def mulPowPrime (p n : ℕ) : ZMod p →+ ZMod (p ^ (n + 1)) :=
  ZMod.lift p
    ⟨{ toFun := fun a : ℤ => (p ^ n : ZMod (p ^ (n + 1))) * a
       map_zero' := by rw [Int.cast_zero, mul_zero]
       map_add' := by intro a b; rw [Int.cast_add, mul_add] }, by
      change ((p : ZMod (p ^ (n + 1))) ^ n) * (p : ℤ) = 0
      rw [Int.cast_natCast, ← pow_succ, ← Nat.cast_pow, ZMod.natCast_self]⟩

theorem mulPowPrime_intCast (p n : ℕ) (a : ℤ) :
    mulPowPrime p n (a : ZMod p) = (p ^ n : ZMod (p ^ (n + 1))) * a :=
  ZMod.lift_coe _ _ _

theorem mulPowPrime_injective {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    Function.Injective (mulPowPrime p n) := by
  apply (injective_iff_map_eq_zero (mulPowPrime p n)).2
  intro z hz
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  rw [mulPowPrime_intCast] at hz
  have hd : (p : ℤ) ^ n * (p : ℤ) ∣ (p : ℤ) ^ n * a := by
    have hz' : (((p : ℤ) ^ n * a : ℤ) : ZMod (p ^ (n + 1))) = 0 := by
      rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      exact hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz'
    simpa only [pow_succ, Nat.cast_mul, Nat.cast_pow] using hz'
  have hpn : (p : ℤ) ^ n ≠ 0 := pow_ne_zero n (Int.ofNat_ne_zero.mpr hp)
  have hdiv : (p : ℤ) ∣ a := (mul_dvd_mul_iff_left hpn).mp hd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact hdiv

/-- Every element killed by reduction modulo p^n is a multiple of p^n. -/
theorem exists_mulPowPrime_eq_of_castHom_eq_zero (p n : ℕ)
    (z : ZMod (p ^ (n + 1)))
    (hz : ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) z = 0) :
    ∃ a : ZMod p, mulPowPrime p n a = z := by
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
  obtain ⟨a, ha⟩ := hz
  refine ⟨(a : ZMod p), ?_⟩
  rw [mulPowPrime_intCast, ha, Int.cast_mul, Int.cast_natCast, Nat.cast_pow]

theorem castHom_mulPowPrime (p n : ℕ) (a : ZMod p) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))
      (mulPowPrime p n a) = 0 := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
  rw [mulPowPrime_intCast, map_mul, map_pow, map_natCast, ← Nat.cast_pow,
    ZMod.natCast_self, zero_mul]

theorem mulPowPrime_mul_castHom (p n : ℕ) (a : ZMod (p ^ (n + 1))) (b : ZMod p) :
    mulPowPrime p n (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p) a * b) =
      a * mulPowPrime p n b := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective b
  rw [map_intCast, ← Int.cast_mul, mulPowPrime_intCast, mulPowPrime_intCast, Int.cast_mul]
  exact mul_left_comm _ _ _

end ZMod
