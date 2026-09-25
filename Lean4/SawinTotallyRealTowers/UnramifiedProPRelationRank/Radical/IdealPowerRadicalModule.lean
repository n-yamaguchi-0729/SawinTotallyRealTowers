/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalExact
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# The ideal-power radical as a finite `ZMod p`-module

For a prime `p`, the empty-support ideal-power radical quotient has exponent
dividing `p`. This file packages its additive presentation as the canonical
`ZMod p`-module, proves finite-dimensionality, and records the resulting
cardinality formulas. The module structure remains explicit and is not
installed as a global instance.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet
open KummerTheory

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The canonical `ZMod p`-module structure on the additive presentation of
the empty-support ideal-power radical quotient. -/
@[reducible]
noncomputable def idealPowerRadicalModPModule :
    Module (ZMod p)
      (Additive (IdealNthPowerRadicalQuotient F
        (p.toPNat (Fact.out : p.Prime).pos))) :=
  additiveZModModuleOfPowEqOne p
    (restrictedRadicalQuotient_pow_eq_one
      (p.toPNat (Fact.out : p.Prime).pos)
      (idealNthPowerRadicalKummerSubgroup F
        (p.toPNat (Fact.out : p.Prime).pos)))

/-- The empty-support ideal-power radical as a `ZMod p`-module object. -/
noncomputable def idealPowerRadicalModP : ModuleCat (ZMod p) := by
  let _ : Module (ZMod p)
      (Additive (IdealNthPowerRadicalQuotient F
        (p.toPNat (Fact.out : p.Prime).pos))) :=
    idealPowerRadicalModPModule F p
  exact ModuleCat.of (ZMod p)
    (Additive (IdealNthPowerRadicalQuotient F
      (p.toPNat (Fact.out : p.Prime).pos)))

/-- The ideal-power radical module is finite-dimensional. -/
theorem idealPowerRadicalModP_finiteDimensional :
    FiniteDimensional (ZMod p) (idealPowerRadicalModP F p) := by
  let _ : Module (ZMod p)
      (Additive (IdealNthPowerRadicalQuotient F
        (p.toPNat (Fact.out : p.Prime).pos))) :=
    idealPowerRadicalModPModule F p
  change Module.Finite (ZMod p)
    (Additive (IdealNthPowerRadicalQuotient F
      (p.toPNat (Fact.out : p.Prime).pos)))
  exact Module.Finite.of_finite

/-- The cardinality of the radical module is `p` to its dimension. -/
theorem card_idealPowerRadicalModP_eq_pow_finrank :
    Nat.card (idealPowerRadicalModP F p) =
      p ^ Module.finrank (ZMod p) (idealPowerRadicalModP F p) := by
  let _ : FiniteDimensional (ZMod p) (idealPowerRadicalModP F p) :=
    idealPowerRadicalModP_finiteDimensional F p
  simpa only [Nat.card_zmod] using
    (Module.natCard_eq_pow_finrank
      (K := ZMod p) (V := idealPowerRadicalModP F p))

/-- The exact unit--radical--class sequence computes the cardinality of the
radical module. -/
theorem card_idealPowerRadicalModP :
    Nat.card (idealPowerRadicalModP F p) =
      p ^ (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F - 1 +
            (if (primitiveRoots p F).Nonempty then 1 else 0)) *
        Nat.card (PClassGroup F p) := by
  change Nat.card
      (IdealNthPowerRadicalQuotient F
        (p.toPNat (Fact.out : p.Prime).pos)) = _
  exact card_idealPthPowerRadicalQuotient F p Fact.out

/-- Equivalently, the arithmetic radical cardinality is `p` to the module
dimension. -/
theorem pow_finrank_idealPowerRadicalModP :
    p ^ Module.finrank (ZMod p) (idealPowerRadicalModP F p) =
      p ^ (NumberField.InfinitePlace.nrRealPlaces F +
          NumberField.InfinitePlace.nrComplexPlaces F - 1 +
            (if (primitiveRoots p F).Nonempty then 1 else 0)) *
        Nat.card (PClassGroup F p) := by
  rw [← card_idealPowerRadicalModP_eq_pow_finrank F p]
  exact card_idealPowerRadicalModP F p

/-- The linear dual of the ideal-power radical module is finite-dimensional. -/
theorem idealPowerRadicalModPDual_finiteDimensional :
    FiniteDimensional (ZMod p)
      (Module.Dual (ZMod p) (idealPowerRadicalModP F p)) := by
  let _ : FiniteDimensional (ZMod p) (idealPowerRadicalModP F p) :=
    idealPowerRadicalModP_finiteDimensional F p
  infer_instance

end ClassFieldTower.Martinet.Shafarevich
