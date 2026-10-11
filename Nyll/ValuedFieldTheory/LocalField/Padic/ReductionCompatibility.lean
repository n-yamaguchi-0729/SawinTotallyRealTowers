/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Compatibility of reduction modulo prime powers and modulo the prime

Reduction from the p-adic integers through a positive prime-power quotient
agrees with their residue map to `ZMod p`.
-/

namespace LocalFieldTheory.DiscreteValuationField

/-- Reducing modulo a positive prime power and then modulo the prime
is the usual p-adic residue map. -/
theorem toZMod_comp_toZModPow (p : ℕ) [Fact p.Prime] (s : ℕ) :
    (ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero s)) (ZMod p)).comp
      (PadicInt.toZModPow (s + 1)) = PadicInt.toZMod := by
  apply ZMod.ringHom_eq_of_ker_eq
  rw [PadicInt.ker_toZMod, RingHom.ker_eq_comap_bot,
    ← IsLocalRing.maximalIdeal_eq_bot (R := ZMod p), IsLocalRing.maximalIdeal_comap]

/-- The same compatibility on the actual unit groups. -/
theorem unitsMap_toZModPow (p : ℕ) [Fact p.Prime] (s : ℕ) (u : ℤ_[p]ˣ) :
    ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero s))
      (Units.map (PadicInt.toZModPow (s + 1)).toMonoidHom u) =
        Units.map PadicInt.toZMod.toMonoidHom u := by
  apply Units.ext
  exact congrArg (fun f : ℤ_[p] →+* ZMod p => f (u : ℤ_[p]))
    (toZMod_comp_toZModPow p s)

end LocalFieldTheory.DiscreteValuationField
