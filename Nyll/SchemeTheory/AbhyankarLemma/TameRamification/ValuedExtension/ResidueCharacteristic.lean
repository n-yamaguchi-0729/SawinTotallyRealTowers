/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Basic

/-!
# Residue characteristic lemmas for tame ramification

This file records the elementary residue-characteristic facts needed for
tower and base-change forms of the tame Abhyankar lemma.  The key point is
that the residue characteristic is unchanged along a valued-field extension,
so "prime to the residue characteristic" can be transported through the
residue-field algebra induced by the extension.
-/

noncomputable section

universe u v w x

namespace ValuationTheory.DiscreteValuationField

namespace DVF

variable {K : Type u} [Field K]

/-- Being prime to the residue characteristic is inherited by divisors. -/
theorem PrimeToResidueCharacteristic.of_dvd
    {F : DVF.{u, v} K} {m n : ℕ}
    (hn : F.PrimeToResidueCharacteristic n) (hmn : m ∣ n) :
    F.PrimeToResidueCharacteristic m := by
  by_cases hchar : F.residueCharacteristic = 0
  · exact Or.inl hchar
  · exact Or.inr <|
      Nat.Coprime.of_dvd_left hmn
        (F.residueCharacteristic_coprime_of_primeToResidueCharacteristic
          hchar hn)

/-- The product of two numbers prime to the residue characteristic is again
prime to the residue characteristic. -/
theorem PrimeToResidueCharacteristic.mul
    {F : DVF.{u, v} K} {m n : ℕ}
    (hm : F.PrimeToResidueCharacteristic m)
    (hn : F.PrimeToResidueCharacteristic n) :
    F.PrimeToResidueCharacteristic (m * n) := by
  by_cases hchar : F.residueCharacteristic = 0
  · exact Or.inl hchar
  · exact Or.inr <|
      Nat.Coprime.mul_left
        (F.residueCharacteristic_coprime_of_primeToResidueCharacteristic
          hchar hm)
        (F.residueCharacteristic_coprime_of_primeToResidueCharacteristic
          hchar hn)

/-- A product is prime to the residue characteristic exactly when both
factors are. -/
theorem primeToResidueCharacteristic_mul_iff
    (F : DVF.{u, v} K) {m n : ℕ} :
    F.PrimeToResidueCharacteristic (m * n) ↔
      F.PrimeToResidueCharacteristic m ∧
        F.PrimeToResidueCharacteristic n := by
  constructor
  · intro hmn
    exact
      ⟨hmn.of_dvd (dvd_mul_right m n),
        hmn.of_dvd (dvd_mul_left n m)⟩
  · intro h
    exact h.1.mul h.2

variable {L : Type w} [Field L]
variable [Algebra K L]
variable {base : DVF.{u, v} K} {target : DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The residue characteristic is unchanged by a valued-field extension. -/
theorem residueCharacteristic_eq_of_hasExtension :
    target.residueCharacteristic = base.residueCharacteristic := by
  rw [DVF.residueCharacteristic_eq_ringChar,
    DVF.residueCharacteristic_eq_ringChar]
  exact (Algebra.ringChar_eq base.residueField target.residueField).symm

/-- Along a valued-field extension, the prime-to-residue-characteristic
condition may be checked on either residue field. -/
theorem primeToResidueCharacteristic_target_iff {n : ℕ} :
    target.PrimeToResidueCharacteristic n ↔
      base.PrimeToResidueCharacteristic n := by
  rw [DVF.PrimeToResidueCharacteristic,
    DVF.PrimeToResidueCharacteristic,
    residueCharacteristic_eq_of_hasExtension (base := base) (target := target)]

/-- Transport a prime-to-residue-characteristic statement from the target
residue field to the base residue field. -/
theorem primeToResidueCharacteristic_of_target {n : ℕ}
    (hn : target.PrimeToResidueCharacteristic n) :
    base.PrimeToResidueCharacteristic n :=
  primeToResidueCharacteristic_target_iff.1 hn

/-- Transport a prime-to-residue-characteristic statement from the base
residue field to the target residue field. -/
theorem primeToResidueCharacteristic_to_target {n : ℕ}
    (hn : base.PrimeToResidueCharacteristic n) :
    target.PrimeToResidueCharacteristic n :=
  primeToResidueCharacteristic_target_iff.2 hn

end DVF

end ValuationTheory.DiscreteValuationField

end
