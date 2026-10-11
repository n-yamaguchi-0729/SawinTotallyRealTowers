/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.ZMod.Basic

/-! # The kernel of reduction modulo p in a p-power residue ring -/

namespace ZMod

/-- Multiplication by `p` embeds residues modulo `p ^ n` into residues modulo
`p ^ (n + 1)`. This additive map is well-defined even though upward casting
is not a ring homomorphism. -/
def mulPow (p n : ℕ) : ZMod (p ^ n) →+ ZMod (p ^ (n + 1)) :=
  ZMod.lift (p ^ n)
    ⟨{ toFun := fun a : ℤ => (p : ZMod (p ^ (n + 1))) * a
       map_zero' := by rw [Int.cast_zero, mul_zero]
       map_add' := by intro a b; rw [Int.cast_add, mul_add] }, by
      change (p : ZMod (p ^ (n + 1))) * ((p ^ n : ℕ) : ℤ) = 0
      rw [Int.cast_natCast, ← Nat.cast_mul, ← pow_succ', ZMod.natCast_self]⟩

theorem mulPow_intCast (p n : ℕ) (a : ℤ) :
    mulPow p n (a : ZMod (p ^ n)) = (p : ZMod (p ^ (n + 1))) * a :=
  ZMod.lift_coe _ _ _

theorem mulPow_injective {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    Function.Injective (mulPow p n) := by
  apply (injective_iff_map_eq_zero (mulPow p n)).2
  intro z hz
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  rw [mulPow_intCast] at hz
  have hd : (p : ℤ) * (p : ℤ) ^ n ∣ (p : ℤ) * a := by
    have hz' : (((p : ℤ) * a : ℤ) : ZMod (p ^ (n + 1))) = 0 := by
      rw [Int.cast_mul, Int.cast_natCast]
      exact hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz'
    simpa only [pow_succ', Nat.cast_mul, Nat.cast_pow] using hz'
  have hpa : (p : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hp
  have hdiv : (p : ℤ) ^ n ∣ a := (mul_dvd_mul_iff_left hpa).mp hd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  simpa only [Nat.cast_pow] using hdiv

/-- The image of multiplication by `p` is the kernel of reduction modulo `p`. -/
theorem exists_mulPow_eq_of_castHom_eq_zero (p n : ℕ)
    (z : ZMod (p ^ (n + 1)))
    (hz : ZMod.castHom (pow_dvd_pow p (Nat.succ_le_succ (Nat.zero_le n)))
      (ZMod (p ^ 1)) z = 0) :
    ∃ a : ZMod (p ^ n), mulPow p n a = z := by
  obtain ⟨b, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, pow_one] at hz
  obtain ⟨a, ha⟩ := hz
  refine ⟨(a : ZMod (p ^ n)), ?_⟩
  rw [mulPow_intCast, ha, Int.cast_mul, Int.cast_natCast]

/-- Multiplication by `p` respects multiplication by a coefficient reduced
from the larger residue ring. -/
theorem mulPow_mul_castHom (p n : ℕ) (a : ZMod (p ^ (n + 1))) (b : ZMod (p ^ n)) :
    mulPow p n (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) a * b) =
      a * mulPow p n b := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
  obtain ⟨j, rfl⟩ := ZMod.intCast_surjective b
  rw [map_intCast, ← Int.cast_mul, mulPow_intCast, mulPow_intCast, Int.cast_mul]
  exact mul_left_comm _ _ _

/-- Reduction commutes with the additive maps given by multiplication by `p`. -/
theorem castHom_mulPow (p n : ℕ) (a : ZMod (p ^ (n + 1))) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ (n + 1))) (ZMod (p ^ (n + 1)))
      (mulPow p (n + 1) a) =
    mulPow p n (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) a) := by
  obtain ⟨i, rfl⟩ := ZMod.intCast_surjective a
  rw [mulPow_intCast, map_mul, map_natCast, map_intCast, map_intCast, mulPow_intCast]

end ZMod
