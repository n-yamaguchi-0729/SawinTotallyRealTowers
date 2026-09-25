/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalModule
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealRadicalCyclotomicBase

set_option autoImplicit false
/-!
# The cyclotomic ideal radical as a `ZMod p`-module

The ideal radical over `F` maps onto the restricted radical generated after
adjoining a primitive `p`-th root of unity.  This file makes that quotient and
the quotient map linear, then dualizes the surjection to a canonical injection
into the dual of the original ideal radical.

All module structures are kept inside explicit definitions; no noncanonical
global instance is installed.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

/-- The canonical `ZMod p`-module structure on the cyclotomic restricted
ideal-radical quotient. -/
@[reducible]
noncomputable def idealRadicalCyclotomicModPModule :
    Module (ZMod p)
      (Additive
        (RestrictedRadicalQuotient (p.toPNat (Fact.out : p.Prime).pos)
          (idealRadicalCyclotomicKummerSubgroup F p Fact.out))) :=
  additiveZModModuleOfPowEqOne p
    (restrictedRadicalQuotient_pow_eq_one
      (p.toPNat (Fact.out : p.Prime).pos)
      (idealRadicalCyclotomicKummerSubgroup F p Fact.out))

/-- The cyclotomic restricted ideal radical as a `ZMod p`-module object. -/
noncomputable def idealRadicalCyclotomicModP : ModuleCat (ZMod p) := by
  letI : Module (ZMod p)
      (Additive
        (RestrictedRadicalQuotient (p.toPNat (Fact.out : p.Prime).pos)
          (idealRadicalCyclotomicKummerSubgroup F p Fact.out))) :=
    idealRadicalCyclotomicModPModule F p
  exact ModuleCat.of (ZMod p)
    (Additive
      (RestrictedRadicalQuotient (p.toPNat (Fact.out : p.Prime).pos)
        (idealRadicalCyclotomicKummerSubgroup F p Fact.out)))

/-- The base-change map on ideal radicals, viewed linearly over `ZMod p`. -/
noncomputable def idealRadicalQuotientToCyclotomicLinearMap :
    idealPowerRadicalModP F p →ₗ[ZMod p]
      idealRadicalCyclotomicModP F p := by
  letI : Module (ZMod p)
      (Additive (IdealNthPowerRadicalQuotient F
        (p.toPNat (Fact.out : p.Prime).pos))) :=
    idealPowerRadicalModPModule F p
  letI : Module (ZMod p)
      (Additive
        (RestrictedRadicalQuotient (p.toPNat (Fact.out : p.Prime).pos)
          (idealRadicalCyclotomicKummerSubgroup F p Fact.out))) :=
    idealRadicalCyclotomicModPModule F p
  exact
    (idealRadicalQuotientToCyclotomicQuotient F p Fact.out).toAdditive.toZModLinearMap p

/-- The linearized base-change map is onto. -/
theorem idealRadicalQuotientToCyclotomicLinearMap_surjective :
    Function.Surjective
      (idealRadicalQuotientToCyclotomicLinearMap F p) := by
  intro y
  obtain ⟨x, hx⟩ :=
    idealRadicalQuotientToCyclotomicQuotient_surjective F p Fact.out
      (Additive.toMul y)
  refine ⟨Additive.ofMul x, ?_⟩
  change Additive.ofMul
      (idealRadicalQuotientToCyclotomicQuotient F p Fact.out x) = y
  exact congrArg Additive.ofMul hx

/-- Dualizing the cyclotomic quotient map gives a canonical linear map into
the dual of the base-field ideal radical. -/
noncomputable def idealRadicalCyclotomicDualInjection :
    Module.Dual (ZMod p) (idealRadicalCyclotomicModP F p) →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP F p) :=
  (idealRadicalQuotientToCyclotomicLinearMap F p).dualMap

/-- The dualized map is injective because the ideal-radical base-change map
is surjective. -/
theorem idealRadicalCyclotomicDualInjection_injective :
    Function.Injective (idealRadicalCyclotomicDualInjection F p) :=
  LinearMap.dualMap_injective_of_surjective
    (idealRadicalQuotientToCyclotomicLinearMap_surjective F p)

/-- The cyclotomic restricted ideal radical is finite-dimensional. -/
theorem idealRadicalCyclotomicModP_finiteDimensional :
    FiniteDimensional (ZMod p) (idealRadicalCyclotomicModP F p) := by
  let _ : FiniteDimensional (ZMod p) (idealPowerRadicalModP F p) :=
    idealPowerRadicalModP_finiteDimensional F p
  exact FiniteDimensional.of_surjective
    (idealRadicalQuotientToCyclotomicLinearMap F p)
    (idealRadicalQuotientToCyclotomicLinearMap_surjective F p)

end ClassFieldTower.Martinet.Shafarevich
