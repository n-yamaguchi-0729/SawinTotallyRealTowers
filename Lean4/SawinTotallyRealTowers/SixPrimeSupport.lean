/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Finset.Insert
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option autoImplicit false

/-!
# The six rational primes allowed in the initial tower

The finite place support is the inverse image of the six primes under
the canonical equivalence between finite places of ℚ and rational primes.
-/

open scoped NumberField
open IsDedekindDomain

namespace ClassFieldTower.Sawin

/-- The rational primes allowed to ramify in the initial tower. -/
def sawinRationalPrimes : Finset ℕ := {3, 5, 7, 11, 13, 17}

/-- The corresponding finite places of ℚ. -/
def sawinRationalPrimeSupport : Set (HeightOneSpectrum (𝓞 ℚ)) :=
  {v | (Rat.HeightOneSpectrum.primesEquiv v : ℕ) ∈ sawinRationalPrimes}

/-- Membership of a rational prime's place is membership in the six-prime set. -/
theorem rationalPrime_mem_sawinRationalPrimeSupport_iff (q : Nat.Primes) :
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ∈
        sawinRationalPrimeSupport ↔ (q : ℕ) ∈ sawinRationalPrimes := by
  simp only [sawinRationalPrimeSupport, Set.mem_ofPred_eq, Equiv.apply_symm_apply]

/-- Two is excluded from the allowed finite ramification support. -/
theorem two_not_mem_sawinRationalPrimeSupport :
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉ sawinRationalPrimeSupport := by
  intro h
  have hTwo : (2 : ℕ) ∈ sawinRationalPrimes :=
    (rationalPrime_mem_sawinRationalPrimeSupport_iff
      (⟨2, Nat.prime_two⟩ : Nat.Primes)).mp h
  exact (by decide : (2 : ℕ) ∉ sawinRationalPrimes) hTwo

end ClassFieldTower.Sawin
