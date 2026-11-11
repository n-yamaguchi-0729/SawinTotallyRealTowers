/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed

/-!
# LubinTate the explicit norm-subgroup computation: the standard level lies in the higher-unit
fixed field
-/



@[expose] public section

universe u v

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]

noncomputable local instance equalCharacteristicHigherUnitMembershipBaseAlgebra
    (F : LocalField.{u, v} K) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField) :=
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra F

noncomputable local instance equalCharacteristicHigherUnitMembershipLevelAlgebra
    (F : LocalField.{u, v} K) (n : ℕ) :
    Algebra F.residueField⸨X⸩
      (equalCharacteristicCompletedLevelField F n) :=
  equalCharacteristicCompletedFrobeniusFixedLevelAlgebra F n

local instance equalCharacteristicHigherUnitMembershipScalarTower
    (F : LocalField.{u, v} K) (n : ℕ) :
    IsScalarTower F.residueField⸨X⸩
      (equalCharacteristicCompletedUnramifiedField F.residueField)
      (equalCharacteristicCompletedLevelField F n) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- States the theorem
`equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit`. -/
theorem
    equalCharacteristicLubinTateLevelFieldToCompleted_mem_fixedField_of_mem_higherUnit
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n)
    (x : equalCharacteristicLubinTateLevelField F n) :
    equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
      equalCharacteristicCompletedFrobeniusFixedField F a n := by
  rw [equalCharacteristicCompletedFrobeniusFixedField,
    IntermediateField.mem_fixedField_iff]
  intro sigma hsigma
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hsigma
  have hfixed :
      equalCharacteristicLubinTateLevelFieldToCompleted F n x ∈
        MulAction.fixedBy (equalCharacteristicCompletedLevelField F n)
          (equalCharacteristicCompletedFrobeniusAlgEquiv F a n) := by
    rw [MulAction.mem_fixedBy]
    exact
      equalCharacteristicCompletedFrobeniusAlgEquiv_comp_levelFieldToCompleted_of_mem_higherUnit
        F a n ha x
  exact MulAction.mem_fixedBy_zpow hfixed j

end EqualCharacteristic
end LubinTate
