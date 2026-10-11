/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Padic.Teichmuller
import Nyll.ValuedFieldTheory.LocalField.Padic.ReductionCompatibility
import Nyll.ValuedFieldTheory.LocalField.Padic.PrimePowerTorsionReduction

/-!
# Teichmüller representatives at finite prime-power levels

A unit modulo a positive power of `p` whose `(p - 1)`-st power is one
is the reduction of the Teichmüller representative of its residue.
-/

namespace LocalFieldTheory.DiscreteValuationField.Examples.Qp

/-- Prime-to-`p` roots of order dividing `p - 1` are recovered by lifting their residue. -/
theorem toZModPow_teichmullerUnits_eq
    (p : ℕ) [Fact p.Prime] (s : ℕ) (u : (ZMod (p ^ (s + 1)))ˣ)
    (hu : u ^ (p - 1) = 1) :
    Units.map (PadicInt.toZModPow (s + 1)).toMonoidHom
      (teichmullerUnits p (ZMod.unitsMap (dvd_pow_self p (Nat.succ_ne_zero s)) u)) = u := by
  have hp : p.Prime := Fact.out
  have hcoprime : (p - 1).Coprime p :=
    ((Nat.coprime_self_sub_right hp.one_le).mpr (Nat.coprime_one_right p)).symm
  apply primePower_units_eq_of_pow_eq_one_of_reduction_eq p s (p - 1) hcoprime
      _ u ?_ hu ?_
  · rw [← map_pow, teichmullerUnits_pow, map_one]
  · rw [unitsMap_toZModPow, toZMod_teichmullerUnits]

end LocalFieldTheory.DiscreteValuationField.Examples.Qp
