/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.UnitTopology
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence

/-!
# LubinTate the explicit norm-subgroup computation: power-series units as Laurent field units

This file packages the genuine composite

`k[[T]]ˣ ≃ 𝒪[k((T))]ˣ → k((T))ˣ`

used in the sharp norm-subgroup calculation.  Its range is the full
valuation-zero unit subgroup, and it carries the explicit Lubin--Tate kernel
to the higher-unit subgroup `U^(n+1)`.  The same composite is definitionally the
Laurent unit multiplying `T` in the changed uniformizer of the completed theta-intertwining theorem.
-/



@[expose] public section

noncomputable section


open scoped LaurentSeries PowerSeries ValuativeRel

universe u v

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

variable {K : Type u} [Field K]

/-- The canonical inclusion of a power-series unit into the Laurent field
unit group, through the actual valuation ring. -/
noncomputable def equalCharacteristicPowerSeriesUnitToLaurentFieldUnit
    (F : LocalField.{u, v} K) :
    F.residueField⟦X⟧ˣ →* F.residueField⸨X⸩ˣ := by
  letI : ValuativeRel F.residueField⸨X⸩ :=
    equalCharacteristicLaurentValuativeRel F
  exact
    (integerUnitsToFieldUnits F.residueField⸨X⸩).comp
      (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
        F.residueField).toMonoidHom

/-- The canonical unit inclusion is the Laurent unit used in the changed
uniformizer `uT` of the completed theta-intertwining theorem. -/
@[simp]
theorem equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_apply
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a =
      equalCharacteristicChangedLaurentUnit F a := by
  apply Units.ext
  rfl

/-- The actual power-series unit factor of a Laurent field unit. The
normalized parameter is `T⁻¹`, so its exponent is the existing valuation map. -/
noncomputable def equalCharacteristicLaurentPowerSeriesUnitPart
    (F : LocalField.{u, v} K) (x : F.residueField⸨X⸩ˣ) :
    F.residueField⟦X⟧ˣ := by
  let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  exact (equalCharacteristicPowerSeriesUnitsEquivLaurentInteger F.residueField).symm
    (uniformizerUnitFactor F.residueField⸨X⸩ (equalCharacteristicLaurentUniformizerUnit F)⁻¹
      (equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F) x)

/-- Including the extracted power-series unit gives exactly the original
unit divided by its normalized uniformizer power. -/
theorem equalCharacteristicLaurentPowerSeriesUnitPart_include
    (F : LocalField.{u, v} K) (x : F.residueField⸨X⸩ˣ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F
        (equalCharacteristicLaurentPowerSeriesUnitPart F x) =
      x / (equalCharacteristicLaurentUniformizerUnit F)⁻¹ ^
        valuationMap F.residueField⸨X⸩ (Additive.ofMul x) := by
  intro valuationOwner localFieldOwner
  change integerUnitsToFieldUnits F.residueField⸨X⸩
      ((equalCharacteristicPowerSeriesUnitsEquivLaurentInteger F.residueField)
        ((equalCharacteristicPowerSeriesUnitsEquivLaurentInteger F.residueField).symm
          (uniformizerUnitFactor F.residueField⸨X⸩
            (equalCharacteristicLaurentUniformizerUnit F)⁻¹
            (equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F) x))) = _
  rw [MulEquiv.apply_symm_apply, integerUnitsToFieldUnits_uniformizerUnitFactor]

/-- The extracted power-series unit and normalized uniformizer power
recover the original Laurent field unit, on the actual unit group. -/
theorem equalCharacteristicLaurentPowerSeriesUnitPart_mul_uniformizer_zpow
    (F : LocalField.{u, v} K) (x : F.residueField⸨X⸩ˣ) :
    let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
    let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
      equalCharacteristicLaurentIsNonarchimedeanLocalField F
    equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F
        (equalCharacteristicLaurentPowerSeriesUnitPart F x) *
        (equalCharacteristicLaurentUniformizerUnit F)⁻¹ ^
          valuationMap F.residueField⸨X⸩ (Additive.ofMul x) = x := by
  intro valuationOwner localFieldOwner
  rw [equalCharacteristicLaurentPowerSeriesUnitPart_include, div_mul_cancel]

/-- Extraction recovers every original power-series unit. In particular it
does not replace the explicit parameter by a chosen representative. -/
theorem equalCharacteristicLaurentPowerSeriesUnitPart_of_powerSeriesUnit
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLaurentPowerSeriesUnitPart F
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a) = a := by
  let : ValuativeRel F.residueField⸨X⸩ := equalCharacteristicLaurentValuativeRel F
  let : IsNonarchimedeanLocalField F.residueField⸨X⸩ :=
    equalCharacteristicLaurentIsNonarchimedeanLocalField F
  let e := equalCharacteristicPowerSeriesUnitsEquivLaurentInteger F.residueField
  apply e.injective
  change e (e.symm (uniformizerUnitFactor F.residueField⸨X⸩
      (equalCharacteristicLaurentUniformizerUnit F)⁻¹
      (equalCharacteristicLaurentUniformizerUnit_inv_valuationMap F)
      (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F a))) = e a
  rw [MulEquiv.apply_symm_apply]
  apply integerUnitsToFieldUnits_injective F.residueField⸨X⸩
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
  change integerUnitsToFieldUnits F.residueField⸨X⸩ (e a) /
      (equalCharacteristicLaurentUniformizerUnit F)⁻¹ ^
        valuationMap F.residueField⸨X⸩
          (Additive.ofMul (integerUnitsToFieldUnits F.residueField⸨X⸩ (e a))) = _
  rw [valuationMap_apply, v_integerUnitsToFieldUnits, zpow_zero, div_one]

/-- In the field unit group, the changed uniformizer is the product of its
power-series unit factor and `T`. -/
theorem equalCharacteristicChangedLaurentUniformizerUnit_eq_unit_mul
    (F : LocalField.{u, v} K) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedLaurentUniformizerUnit F a =
      equalCharacteristicChangedLaurentUnit F a *
        equalCharacteristicLaurentUniformizerUnit F := by
  apply Units.ext
  exact equalCharacteristicChangedLaurentUniformizer_eq_unit_mul F a

/-- Multiplication by `T` does not change norm membership for a Lubin--Tate
level, because both `T⁻¹` and `T` are already norms.  Thus the prime norm
`uT` used in the completed theta-intertwining theorem detects exactly whether the unit `u` is a
norm. -/
theorem equalCharacteristicChangedLaurentUniformizerUnit_mem_normSubgroup_iff
    {K₀ : Type u} [Field K₀]
    (F : LocalField.{u, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicChangedLaurentUniformizerUnit F a ∈
        equalCharacteristicLubinTateNormSubgroup F n ↔
      equalCharacteristicChangedLaurentUnit F a ∈
        equalCharacteristicLubinTateNormSubgroup F n := by
  let N := equalCharacteristicLubinTateNormSubgroup F n
  let T := equalCharacteristicLaurentUniformizerUnit F
  have hTinv : T⁻¹ ∈ N :=
    equalCharacteristicLubinTate_normalizedUniformizer_mem_normSubgroup F n
  have hT : T ∈ N := by
    simpa using N.inv_mem hTinv
  constructor
  · intro hprod
    rw [equalCharacteristicChangedLaurentUniformizerUnit_eq_unit_mul] at hprod
    have h := N.mul_mem hprod hTinv
    change equalCharacteristicChangedLaurentUnit F a ∈ N
    simpa [T, mul_assoc] using h
  · intro hu
    rw [equalCharacteristicChangedLaurentUniformizerUnit_eq_unit_mul]
    change
      equalCharacteristicChangedLaurentUnit F a * T ∈ N
    exact N.mul_mem hu hT

/-- The positive-valuation inverse prime norm used by the normalized
normalized additive valuation has the same norm-membership test. -/
theorem equalCharacteristicChangedLaurentUniformizerUnit_inv_mem_normSubgroup_iff
    {K₀ : Type u} [Field K₀]
    (F : LocalField.{u, v} K₀)
    [CharP K₀ F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    (equalCharacteristicChangedLaurentUniformizerUnit F a)⁻¹ ∈
        equalCharacteristicLubinTateNormSubgroup F n ↔
      equalCharacteristicChangedLaurentUnit F a ∈
        equalCharacteristicLubinTateNormSubgroup F n := by
  let N := equalCharacteristicLubinTateNormSubgroup F n
  constructor
  · intro hinv
    apply
      (equalCharacteristicChangedLaurentUniformizerUnit_mem_normSubgroup_iff
        F n a).1
    simpa using N.inv_mem hinv
  · intro hu
    exact N.inv_mem
      ((equalCharacteristicChangedLaurentUniformizerUnit_mem_normSubgroup_iff
        F n a).2 hu)

/-- Every valuation-zero Laurent field unit, and only such a unit, comes
from a power-series unit under the canonical inclusion. -/
theorem equalCharacteristicPowerSeriesUnitToLaurentFieldUnit_range
    (F : LocalField.{u, v} K) :
    let : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    MonoidHom.range (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F) =
      LocalFieldTheory.localBaseUnitSubgroup F.residueField⸨X⸩ := by
  intro sharedOwner1
  let e := equalCharacteristicPowerSeriesUnitsEquivLaurentInteger
    F.residueField
  change MonoidHom.range
      ((integerUnitsToFieldUnits F.residueField⸨X⸩).comp e.toMonoidHom) =
    MonoidHom.range (integerUnitsToFieldUnits F.residueField⸨X⸩)
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨e a, rfl⟩
  · rintro ⟨b, rfl⟩
    refine ⟨e.symm b, ?_⟩
    exact congrArg (integerUnitsToFieldUnits F.residueField⸨X⸩) (e.apply_symm_apply b)

/-- The explicit Lubin--Tate higher-unit kernel maps to the canonical field
principal-unit group `U^(n+1)` in one step. -/
theorem equalCharacteristicLubinTateHigherUnitSubgroup_map_toLaurentField_eq
    (F : LocalField.{u, v} K) (n : ℕ) :
    let : ValuativeRel F.residueField⸨X⸩ :=
      equalCharacteristicLaurentValuativeRel F
    (equalCharacteristicLubinTateHigherUnitSubgroup F n).map
        (equalCharacteristicPowerSeriesUnitToLaurentFieldUnit F) =
      LocalFieldTheory.fieldPrincipalUnits F.residueField⸨X⸩ (n + 1) := by
  intro sharedOwner1
  simpa only [equalCharacteristicPowerSeriesUnitToLaurentFieldUnit,
    Subgroup.map_map] using
    (equalCharacteristicLubinTateHigherUnitSubgroup_map_eq_fieldPrincipalUnits
      F n)

end EqualCharacteristic
end LubinTate
