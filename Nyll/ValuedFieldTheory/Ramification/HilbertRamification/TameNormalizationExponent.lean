/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# The actual tame-character normalization exponent

The two inertia-cardinality formulas and the actual tame-degree divisibility
show that the ratio of the ramification index to the tame degree divides the
wild order. Thus it is a residue-characteristic power, and is prime to the
tame degree. No residue-separability assertion is needed for this arithmetic.
-/

namespace RamificationTheory.HilbertRamification

private theorem divisor_of_normalization_factor
    {n e w f : ℕ} (hn : 0 < n) (hne : n ∣ e) (horder : n * w = e * f) :
    e / n ∣ w := by
  refine ⟨f, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left hn
  calc
    n * w = e * f := horder
    _ = (n * (e / n)) * f :=
      congrArg (fun z : ℕ => z * f)
        ((Nat.mul_comm n (e / n)).trans (Nat.div_mul_cancel hne)).symm
    _ = n * ((e / n) * f) := Nat.mul_assoc n (e / n) f

/-- The normalization exponent is a characteristic power when the wild
order is a characteristic power. The inseparable residue factor can remain
arbitrary in the supplied actual cardinality identity. -/
theorem tameNormalizationExponent_eq_prime_pow
    {p n e w f a : ℕ} (hp : Nat.Prime p) (hn : 0 < n)
    (hne : n ∣ e) (horder : n * w = e * f) (hw : w = p ^ a) :
    ∃ b : ℕ, e / n = p ^ b := by
  have hdiv : e / n ∣ p ^ a :=
    hw ▸ divisor_of_normalization_factor hn hne horder
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp hdiv
  exact ⟨b, hb⟩

/-- The actual normalization power is invertible modulo the tame degree. -/
theorem tameNormalizationExponent_coprime
    {p n e w f a : ℕ} (hp : Nat.Prime p) (hn : 0 < n)
    (hne : n ∣ e) (horder : n * w = e * f) (hw : w = p ^ a)
    (hnp : Nat.Coprime n p) : Nat.Coprime n (e / n) := by
  obtain ⟨b, hb⟩ := tameNormalizationExponent_eq_prime_pow hp hn hne horder hw
  rw [hb]
  exact hnp.pow_right b

/-- Trivial wild inertia forces the actual normalization exponent to be one. -/
theorem tameNormalizationExponent_eq_one_of_wild_eq_one
    {n e w f : ℕ} (hn : 0 < n) (hne : n ∣ e)
    (horder : n * w = e * f) (hw : w = 1) : e / n = 1 := by
  exact Nat.dvd_one.mp (hw ▸ divisor_of_normalization_factor hn hne horder)

end RamificationTheory.HilbertRamification
