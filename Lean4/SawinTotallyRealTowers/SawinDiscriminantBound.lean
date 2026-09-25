/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.NumberField.SupportedDiscriminantBound
import SawinTotallyRealTowers.RationalRamificationSupport
import SawinTotallyRealTowers.SixPrimeSupport
import SawinTotallyRealTowers.RamificationSupport
import Mathlib.GroupTheory.PGroup
import Mathlib.FieldTheory.Galois.Basic

set_option autoImplicit false

/-!
# A uniform discriminant bound for the initial Sawin tower

The degree of every finite admissible layer is a power of two. Its
ramified rational primes belong to {3,5,7,11,13,17}, whose product is
255255. The prime-to-degree different bound gives the same root scale
255255 for every such finite Galois layer.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace ClassFieldTower.Sawin

/-- The initial tower's arithmetic conditions give a discriminant bound
with one constant for all finite Galois number fields satisfying them. -/
theorem discr_natAbs_le_of_sawin_ramification
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (hP : IsPGroup 2 Gal(L/ℚ))
    (hOutside : IsUnramifiedAtFinitePlacesOutside ℚ L sawinRationalPrimeSupport) :
    (NumberField.discr L).natAbs ≤ 255255 ^ Module.finrank ℚ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  rw [IsGalois.card_aut_eq_finrank] at ha
  apply AlgebraicNumberTheory.Discriminant.natAbs_discr_le_pow_of_coprime_support
    L 255255 (by decide)
  · rw [ha]
    exact Nat.Coprime.pow_right a (by decide : Nat.Coprime 255255 2)
  · intro q hq
    have hmem := (rationalPrime_mem_sawinRationalPrimeSupport_iff q).mp
      ((isUnramifiedAtFinitePlacesOutside_rat_iff_discr L sawinRationalPrimeSupport).mp
        hOutside q hq)
    have hProd : ∏ p ∈ sawinRationalPrimes, p = 255255 := by decide
    rw [← hProd]
    exact Finset.dvd_prod_of_mem (fun p : ℕ ↦ p) hmem

end ClassFieldTower.Sawin
