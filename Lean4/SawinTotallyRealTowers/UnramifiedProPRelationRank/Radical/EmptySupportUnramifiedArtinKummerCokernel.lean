/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceUnramifiedArtinKummerLocalization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceValuationDiagonal

set_option autoImplicit false
/-!
# The empty-support unramified Artin--Kummer cokernel

Over a number field containing the coefficient roots of unity (in particular
the chosen cyclotomic base), actual local Artin--Kummer pairing against
intrinsic unramified `H¹` assembles into a global localization map on Kummer
power classes.  Its dual has the same image as finite-valuation localization,
so its cokernel is canonically the dual of the ideal-power radical.

This uses the dual of the unramified local subspace as localization target;
it does not identify the different ramified-quotient model
`EmptySupportCohomologicalH1Cokernel` with the arithmetic cokernel.
-/

open NumberField IsDedekindDomain
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type) [Field K] [NumberField K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

/-- The kernel of actual unramified Artin--Kummer localization agrees
with the kernel of arithmetic finite-valuation localization. -/
theorem finitePlaceUnramifiedArtinKummerLocalizationFamily_ker_eq_valuation
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    LinearMap.ker (finitePlaceUnramifiedArtinKummerLocalizationFamily K n hmu) =
      LinearMap.ker (absolutePowerClassFiniteValuationLocalization K (n : ℕ)) := by
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker,
    finitePlaceUnramifiedArtinKummerLocalizationFamily_eq_zero_iff]
  constructor
  · intro hx
    apply Additive.toMul.injective
    funext v
    change v.valuationOfNeZeroMod (n : ℕ) (Additive.toMul x) = 1
    apply Multiplicative.toAdd.injective
    change (v.valuationOfNeZeroMod (n : ℕ) (Additive.toMul x)).toAdd = 0
    rw [← finitePlaceLocalPowerClassValuation_localization K (n : ℕ) v x]
    exact hx v
  · intro hx v
    rw [finitePlaceLocalPowerClassValuation_localization]
    exact congrArg
      (fun z : FiniteValuationDefectModP K (n : ℕ) ↦ (Additive.toMul z v).toAdd) hx

/-- The global Kummer classes annihilating every intrinsic unramified
local class are exactly the ideal-power radical. -/
theorem finitePlaceUnramifiedArtinKummerLocalizationFamily_ker
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    LinearMap.ker (finitePlaceUnramifiedArtinKummerLocalizationFamily K n hmu) =
      LinearMap.range (idealPowerRadicalToAbsolutePowerClassLinearMap K (n : ℕ)) := by
  rw [finitePlaceUnramifiedArtinKummerLocalizationFamily_ker_eq_valuation,
    absolutePowerClassFiniteValuationLocalization_ker]

/-- The dual local-to-global map assembled from the actual unramified
local Artin--Kummer pairings. -/
noncomputable def finitePlaceUnramifiedArtinKummerLocalizationFamilyDual
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    Module.Dual (ZMod (n : ℕ))
        (FinitePlaceUnramifiedArtinKummerLocalizationTarget K n) →ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP K (n : ℕ)) :=
  (finitePlaceUnramifiedArtinKummerLocalizationFamily K n hmu).dualMap

/-- The dual of the actual unramified local pairing family has exactly
the same image as the arithmetic finite-valuation dual map. -/
theorem finitePlaceUnramifiedArtinKummerLocalizationFamilyDual_range
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    LinearMap.range (finitePlaceUnramifiedArtinKummerLocalizationFamilyDual K n hmu) =
      LinearMap.range (finiteValuationLocalizationDual K (n : ℕ)) := by
  rw [finitePlaceUnramifiedArtinKummerLocalizationFamilyDual,
    finiteValuationLocalizationDual,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    finitePlaceUnramifiedArtinKummerLocalizationFamily_ker_eq_valuation]

/-- The empty-support cokernel obtained by dualizing localization against
actual unramified local `H¹`, with global `H¹(μ_n)` in its Kummer model. -/
abbrev EmptySupportUnramifiedArtinKummerCokernel
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) : ModuleCat (ZMod (n : ℕ)) :=
  ModuleCat.of (ZMod (n : ℕ))
    (Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP K (n : ℕ)) ⧸
      LinearMap.range (finitePlaceUnramifiedArtinKummerLocalizationFamilyDual K n hmu))

/-- The actual unramified Artin--Kummer cokernel is the arithmetic
empty-support Kummer cokernel. -/
noncomputable def emptySupportUnramifiedArtinKummerCokernelEquivKummer
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    EmptySupportUnramifiedArtinKummerCokernel K n hmu ≃ₗ[ZMod (n : ℕ)]
      EmptySupportKummerCokernel K (n : ℕ) :=
  Submodule.quotEquivOfEq _ _
    (finitePlaceUnramifiedArtinKummerLocalizationFamilyDual_range K n hmu)

/-- Hence the unramified Artin--Kummer cokernel is the linear dual of
the ideal-power radical. -/
noncomputable def emptySupportUnramifiedArtinKummerCokernelEquivIdealPowerRadicalDual
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) :
    EmptySupportUnramifiedArtinKummerCokernel K n hmu ≃ₗ[ZMod (n : ℕ)]
      Module.Dual (ZMod (n : ℕ)) (idealPowerRadicalModP K (n : ℕ)) :=
  (emptySupportUnramifiedArtinKummerCokernelEquivKummer K n hmu).trans
    (emptySupportKummerCokernelEquivIdealPowerRadicalDual K (n : ℕ))

@[simp]
theorem emptySupportUnramifiedArtinKummerCokernelEquivIdealPowerRadicalDual_mk
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (phi : Module.Dual (ZMod (n : ℕ)) (absolutePowerClassModP K (n : ℕ))) :
    emptySupportUnramifiedArtinKummerCokernelEquivIdealPowerRadicalDual K n hmu
        (Submodule.Quotient.mk phi) =
      absolutePowerClassDualRestriction K (n : ℕ) phi := by
  change emptySupportKummerCokernelEquivIdealPowerRadicalDual K (n : ℕ)
      (Submodule.Quotient.mk phi) = _
  exact emptySupportKummerCokernelEquivIdealPowerRadicalDual_mk K (n : ℕ) phi

end ClassFieldTower.Martinet.Shafarevich
