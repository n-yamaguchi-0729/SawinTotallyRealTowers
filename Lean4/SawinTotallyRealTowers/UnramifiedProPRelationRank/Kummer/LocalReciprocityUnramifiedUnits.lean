/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.LocalReciprocityUnramifiedValuation

set_option autoImplicit false
/-!
# Integral-unit triviality detects unramified local characters

The actual unit/uniformizer decomposition shows that an Artin character
trivial on all integer units has a valuation-line power-class functional.
The roots-of-unity-free reciprocity range theorem and pairing injectivity
then identify it with the intrinsic unramified H¹ submodule. Neither
characteristic zero nor a primitive root in the local field is assumed.
-/

open scoped Topology ValuativeRel

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP LocalClassFieldTheory LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (n : ℕ+) [Fact ((n : ℕ).Prime)]

local instance localReciprocityUnitsTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance localReciprocityUnitsDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance localReciprocityUnitsH1Module :
    Module (ZMod (n : ℕ))
      (ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :=
  continuousH1ZModModule

/-- An Artin character trivial on integer units is its normalized
uniformizer coordinate times valuation. -/
theorem localReciprocityH1PowerClassPairing_eq_valuation_of_integerUnits
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K))
    (hchi : ∀ u : 𝒪[K]ˣ,
      localReciprocityUnitCharacter K (n : ℕ) chi (integerUnitsToFieldUnits K u) = 1) :
    localReciprocityH1PowerClassPairing K (n : ℕ) chi =
      localPowerClassValuationDualEmbedding K (n : ℕ) (localReciprocityPrimeScalar K n chi) := by
  let π := inverseIntegerRingUniformizerFieldUnit K
  have hπ : valuationMap K (Additive.ofMul π) = 1 :=
    v_inverseIntegerRingUniformizerFieldUnit K
  let f := localReciprocityUnitCharacter K (n : ℕ) chi
  have hc : localReciprocityPrimeScalar K n chi = (f π).toAdd :=
    localReciprocityH1PowerClassPairing_mk K (n : ℕ) chi π
  have hformula (a : Kˣ) :
      localReciprocityH1PowerClassPairing K (n : ℕ) chi
        (Additive.ofMul (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)) =
      localReciprocityPrimeScalar K n chi *
        (valuationMap K (Additive.ofMul a) : ZMod (n : ℕ)) := by
    let qa : absolutePowerClassModP K (n : ℕ) :=
      Additive.ofMul
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
    change
      (localReciprocityH1PowerClassPairing K (n : ℕ) chi) qa =
        localReciprocityPrimeScalar K n chi *
          (valuationMap K (Additive.ofMul a) : ZMod (n : ℕ))
    obtain ⟨u, hu⟩ := exists_integerUnit_mul_uniformizer_zpow K π hπ a
    have hf : f a = f π ^ valuationMap K (Additive.ofMul a) := by
      calc
        f a = f (integerUnitsToFieldUnits K u * π ^ valuationMap K (Additive.ofMul a)) :=
          congrArg f hu.symm
        _ = _ := by
          rw [map_mul, hchi, one_mul, map_zpow]
          rfl
    calc
      _ = (f a).toAdd := localReciprocityH1PowerClassPairing_mk K (n : ℕ) chi a
      _ = _ := by rw [hf, toAdd_zpow, zsmul_eq_mul, hc, mul_comm]
  apply LinearMap.ext
  intro x
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range x.toMul
  let qa : absolutePowerClassModP K (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)
  have hqa : x = qa := congrArg Additive.ofMul ha.symm
  rw [hqa]
  change
    (localReciprocityH1PowerClassPairing K (n : ℕ) chi) qa =
      (localPowerClassValuationDualEmbedding K (n : ℕ)
        (localReciprocityPrimeScalar K n chi)) qa
  rw [localPowerClassValuationDualEmbedding_apply]
  dsimp only [qa]
  rw [localPowerClassValuation_mk]
  exact hformula a

/-- A local Artin character kills every integer unit exactly when its
continuous H¹ class is intrinsically unramified. -/
theorem localReciprocityUnitCharacter_integerUnits_iff_unramified
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :
    (∀ u : 𝒪[K]ˣ,
      localReciprocityUnitCharacter K (n : ℕ) chi (integerUnitsToFieldUnits K u) = 1) ↔
      chi ∈ localStandardUnramifiedH1 K n := by
  constructor
  · intro hchi
    have hmem : localReciprocityH1PowerClassPairing K (n : ℕ) chi ∈
        LinearMap.range ((localReciprocityH1PowerClassPairing K (n : ℕ)).comp
          (localStandardUnramifiedH1 K n).subtype) := by
      rw [localReciprocityH1PowerClassPairing_unramified_range K n]
      exact ⟨localReciprocityPrimeScalar K n chi,
        (localReciprocityH1PowerClassPairing_eq_valuation_of_integerUnits K n chi hchi).symm⟩
    obtain ⟨psi, hpsi⟩ := hmem
    have heq := localReciprocityH1PowerClassPairing_injective K (n : ℕ) hpsi
    exact heq ▸ psi.property
  · intro hchi u
    obtain ⟨c, hc⟩ := localReciprocityH1PowerClassPairing_mem_valuation_range K n chi hchi
    let qu : absolutePowerClassModP K (n : ℕ) :=
      Additive.ofMul
        (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range
          (integerUnitsToFieldUnits K u))
    apply Multiplicative.toAdd.injective
    change (localReciprocityH1PowerClassPairing K (n : ℕ) chi) qu = 0
    rw [← hc, localPowerClassValuationDualEmbedding_apply]
    dsimp only [qu]
    rw [localPowerClassValuation_mk,
      valuationMap_apply, v_integerUnitsToFieldUnits, Int.cast_zero, mul_zero]

/-- Equivalent valuation-zero formulation, convenient for comparing
actual integral-unit subgroups under completion normalizations. -/
theorem localReciprocityUnitCharacter_valuationZero_iff_unramified
    (chi : ContinuousH1ZMod (p := (n : ℕ)) (G := Field.absoluteGaloisGroup K)) :
    (∀ a : Kˣ, valuationMap K (Additive.ofMul a) = 0 →
      localReciprocityUnitCharacter K (n : ℕ) chi a = 1) ↔
      chi ∈ localStandardUnramifiedH1 K n := by
  rw [← localReciprocityUnitCharacter_integerUnits_iff_unramified K n chi]
  constructor
  · intro h u
    exact h _ (v_integerUnitsToFieldUnits K u)
  · intro h a ha
    obtain ⟨u, rfl⟩ :=
      (integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero K a).2 ha
    exact h u

end ClassFieldTower.Martinet.Shafarevich
