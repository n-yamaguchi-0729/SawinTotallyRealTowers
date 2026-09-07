import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective

set_option autoImplicit false

/-!
# LubinTate the explicit norm-subgroup computation: the standard level is the higher-unit fixed field

The standard-level embedding is an equivalence because its source and target
have the same degree `(q - 1) q^n`.
-/

noncomputable section


open scoped LaurentSeries PowerSeries

namespace LubinTate
namespace EqualCharacteristic

open LocalFieldTheory.DiscreteValuationField

variable {K : Type} [Field K]

attribute [local instance]
  equalCharacteristicCompletedFrobeniusFixedBaseAlgebra
  equalCharacteristicLubinTateLevelFieldAlgebra
  equalCharacteristicLubinTateLevelFieldSMul
  equalCharacteristicLubinTateLevelFieldModule
  equalCharacteristicCompletedFrobeniusFixedFieldAlgebra
  equalCharacteristicCompletedFrobeniusFixedFieldSMul
  equalCharacteristicCompletedFrobeniusFixedFieldModule

/-- Defines `equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit`. -/
noncomputable def
    equalCharacteristicLubinTateLevelFieldEquivFixedFieldOfHigherUnit
    (F : LocalField K)
    [CharP K F.residueCharacteristic]
    (a : F.residueField⟦X⟧ˣ) (n : ℕ)
    (ha : a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n) :
    @AlgEquiv
      F.residueField⸨X⸩
      ↥(equalCharacteristicLubinTateLevelField F n)
      ↥(equalCharacteristicCompletedFrobeniusFixedField F a n)
      inferInstance
      inferInstance
      inferInstance
      (equalCharacteristicLubinTateLevelFieldAlgebra F n)
      (equalCharacteristicCompletedFrobeniusFixedFieldAlgebra F a n) :=
  AlgEquiv.ofBijective
    (equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit F a n ha)
    ⟨fun _ _ h =>
      (equalCharacteristicLubinTateLevelFieldToCompletedRingHom F n).injective
        (congrArg Subtype.val h),
      equalCharacteristicLubinTateLevelFieldToFixedFieldOfHigherUnit_surjective
        F a n ha⟩

end EqualCharacteristic
end LubinTate
