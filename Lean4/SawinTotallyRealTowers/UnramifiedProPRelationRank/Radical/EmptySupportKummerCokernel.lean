/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalAbsoluteKummerLinear
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# The empty-support Kummer cokernel

The finite valuations give a concrete localization map from global power classes to the product
of their valuation defects.  Its kernel is exactly the ideal-power radical.  Dualizing the
localization map therefore gives an actual presentation of the empty-support Kummer cokernel,
and the first isomorphism theorem identifies that cokernel with the dual of the ideal-power
radical.

This is the algebraic Kummer model of `B_∅`.  Identifying its localization-dual map with the
cohomological map assembled from local unramified `H¹` still requires local Tate duality and
global-to-local restriction maps.
-/

open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open IsDedekindDomain KummerTheory

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]

/-- The multiplicative product of the mod-`p` finite-valuation defects. -/
abbrev FiniteValuationDefect :=
  ∀ _v : HeightOneSpectrum (𝓞 K), Multiplicative (ZMod p)

omit [NumberField K] in
/-- Every product of mod-`p` valuation defects has exponent dividing `p`. -/
theorem finiteValuationDefect_pow_eq_one
    (x : FiniteValuationDefect K p) :
    x ^ p = 1 := by
  funext v
  apply Multiplicative.ofAdd.injective
  change p • (x v).toAdd = 0
  simp

/-- The product of the mod-`p` finite-valuation defects as a `ZMod p`-module. -/
noncomputable def FiniteValuationDefectModP : ModuleCat (ZMod p) := by
  letI : Module (ZMod p) (Additive (FiniteValuationDefect K p)) :=
    additiveZModModuleOfPowEqOne p
      (finiteValuationDefect_pow_eq_one K p)
  exact ModuleCat.of (ZMod p) (Additive (FiniteValuationDefect K p))

/-- Multiplicative localization of a global power class at every finite valuation. -/
def absolutePowerClassFiniteValuationLocalizationMonoidHom :
    (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
      FiniteValuationDefect K p :=
  MonoidHom.pi fun v ↦ v.valuationOfNeZeroMod p

/-- Localization of a global power class at every finite valuation. -/
noncomputable def absolutePowerClassFiniteValuationLocalization :
    absolutePowerClassModP K p →ₗ[ZMod p] FiniteValuationDefectModP K p := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  letI : Module (ZMod p) (Additive (FiniteValuationDefect K p)) :=
    additiveZModModuleOfPowEqOne p
      (finiteValuationDefect_pow_eq_one K p)
  exact
    (absolutePowerClassFiniteValuationLocalizationMonoidHom K p).toAdditive.toZModLinearMap p

@[simp]
theorem absolutePowerClassFiniteValuationLocalization_apply
    (x : absolutePowerClassModP K p)
    (v : HeightOneSpectrum (𝓞 K)) :
    Additive.toMul (absolutePowerClassFiniteValuationLocalization K p x) v =
      v.valuationOfNeZeroMod p (Additive.toMul x) :=
  rfl

/-- The kernel of finite-valuation localization is precisely the embedded ideal-power radical. -/
theorem absolutePowerClassFiniteValuationLocalization_ker :
    LinearMap.ker (absolutePowerClassFiniteValuationLocalization K p) =
      LinearMap.range (idealPowerRadicalToAbsolutePowerClassLinearMap K p) := by
  ext x
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have hval : ∀ v : HeightOneSpectrum (𝓞 K),
        v.valuationOfNeZeroMod p (Additive.toMul x) = 1 := by
      intro v
      have hv := congrArg
        (fun z : FiniteValuationDefectModP K p ↦ Additive.toMul z v) hx
      exact hv
    let s : EmptySupportSelmerGroup K
        (p.toPNat (Fact.out : p.Prime).pos) :=
      ⟨Additive.toMul x, fun v _hv ↦ hval v⟩
    let y : IdealNthPowerRadicalQuotient K
        (p.toPNat (Fact.out : p.Prime).pos) :=
      (idealNthPowerRadicalQuotientEquivEmptySelmer K
        (p.toPNat (Fact.out : p.Prime).pos)).symm s
    refine ⟨Additive.ofMul y, ?_⟩
    apply Additive.toMul.injective
    change
      emptySupportSelmerToAbsolutePowerClass K
          (p.toPNat (Fact.out : p.Prime).pos)
          (idealNthPowerRadicalQuotientEquivEmptySelmer K
            (p.toPNat (Fact.out : p.Prime).pos) y) =
        Additive.toMul x
    rw [show idealNthPowerRadicalQuotientEquivEmptySelmer K
      (p.toPNat (Fact.out : p.Prime).pos) y = s by
        exact (idealNthPowerRadicalQuotientEquivEmptySelmer K
          (p.toPNat (Fact.out : p.Prime).pos)).apply_symm_apply s]
    rfl
  · rintro ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    apply Additive.toMul.injective
    funext v
    change
      v.valuationOfNeZeroMod p
        ((idealNthPowerRadicalQuotientEquivEmptySelmer K
          (p.toPNat (Fact.out : p.Prime).pos) (Additive.toMul y)).1) = 1
    have hv :=
      (idealNthPowerRadicalQuotientEquivEmptySelmer K
        (p.toPNat (Fact.out : p.Prime).pos) (Additive.toMul y)).property
          v (Set.notMem_empty v)
    exact hv

/-- The dual of finite-valuation localization.  Its image consists of global Kummer functionals
generated by the finite-valuation defects. -/
noncomputable def finiteValuationLocalizationDual :
    Module.Dual (ZMod p) (FiniteValuationDefectModP K p) →ₗ[ZMod p]
      Module.Dual (ZMod p) (absolutePowerClassModP K p) :=
  (absolutePowerClassFiniteValuationLocalization K p).dualMap

/-- Restriction of global Kummer functionals to the ideal-power radical. -/
noncomputable def absolutePowerClassDualRestriction :
    Module.Dual (ZMod p) (absolutePowerClassModP K p) →ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP K p) :=
  (idealPowerRadicalToAbsolutePowerClassLinearMap K p).dualMap

/-- Every functional on the ideal-power radical extends to the full power-class module. -/
theorem absolutePowerClassDualRestriction_surjective :
    Function.Surjective (absolutePowerClassDualRestriction K p) :=
  LinearMap.dualMap_surjective_of_injective
    (idealPowerRadicalToAbsolutePowerClassLinearMap_injective K p)

/-- The image of dualized finite-valuation localization is exactly the kernel of restriction to
the ideal-power radical. -/
theorem finiteValuationLocalizationDual_range :
    LinearMap.range (finiteValuationLocalizationDual K p) =
      LinearMap.ker (absolutePowerClassDualRestriction K p) := by
  calc
    LinearMap.range (finiteValuationLocalizationDual K p) =
        (LinearMap.ker
          (absolutePowerClassFiniteValuationLocalization K p)).dualAnnihilator :=
      LinearMap.range_dualMap_eq_dualAnnihilator_ker _
    _ = (LinearMap.range
          (idealPowerRadicalToAbsolutePowerClassLinearMap K p)).dualAnnihilator := by
      rw [absolutePowerClassFiniteValuationLocalization_ker K p]
    _ = LinearMap.ker (absolutePowerClassDualRestriction K p) :=
      (LinearMap.ker_dualMap_eq_dualAnnihilator_range
        (f := idealPowerRadicalToAbsolutePowerClassLinearMap K p)).symm

/-- The cokernel of dualized finite-valuation localization: the algebraic Kummer model of
`B_∅`. -/
abbrev EmptySupportKummerCokernel : ModuleCat (ZMod p) :=
  ModuleCat.of (ZMod p)
    (Module.Dual (ZMod p) (absolutePowerClassModP K p) ⧸
      LinearMap.range (finiteValuationLocalizationDual K p))

/-- The empty-support Kummer cokernel is the dual of the ideal-power radical. -/
noncomputable def emptySupportKummerCokernelEquivIdealPowerRadicalDual :
    EmptySupportKummerCokernel K p ≃ₗ[ZMod p]
      Module.Dual (ZMod p) (idealPowerRadicalModP K p) :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (finiteValuationLocalizationDual K p))
      (LinearMap.ker (absolutePowerClassDualRestriction K p))
      (finiteValuationLocalizationDual_range K p)).trans
    ((absolutePowerClassDualRestriction K p).quotKerEquivOfSurjective
      (absolutePowerClassDualRestriction_surjective K p))

@[simp]
theorem emptySupportKummerCokernelEquivIdealPowerRadicalDual_mk
    (φ : Module.Dual (ZMod p) (absolutePowerClassModP K p)) :
    emptySupportKummerCokernelEquivIdealPowerRadicalDual K p
        (Submodule.Quotient.mk φ) =
      absolutePowerClassDualRestriction K p φ :=
  by
    simp [emptySupportKummerCokernelEquivIdealPowerRadicalDual]

end ClassFieldTower.Martinet.Shafarevich
