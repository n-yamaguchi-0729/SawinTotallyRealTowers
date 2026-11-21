/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.GlobalClassFields.ClassFieldRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleClassSystem
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldNormResidue

/-!
# Number field structures on rational fixed field presentations

These finite-dimensional, number field and Galois structures are used in
the explicit rational cyclotomic realizations of abstract fixed fields.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace GlobalClassFields

open ClassFormation
open LocalClassFieldTheory
open Reciprocity

/-- Use the same rational algebra structure as the ordinary correspondence
when constructing all named fixed-field carriers below. -/
noncomputable local instance
    finiteAbelianClassFieldCorrespondence_separableClosureAlgebra :
    Algebra ℚ (SeparableClosure ℚ) :=
  numberFieldSeparableClosureAlgebra ℚ

noncomputable instance ordinaryIdeleClassNormBaseFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    FiniteDimensional ℚ (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  abstractFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ) K.field K.finite

noncomputable instance ordinaryIdeleClassNormExtensionFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_finiteDimensional
    ℚ (SeparableClosure ℚ)
    K.field L.field L.below K.finite L.finite

noncomputable instance ordinaryIdeleClassNormScalarTower
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsScalarTower ℚ
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below) :=
  IsScalarTower.of_algebraMap_eq' rfl

noncomputable instance ordinaryIdeleClassNormExtensionAbsoluteFiniteDimensional
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    FiniteDimensional ℚ
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below) :=
  FiniteDimensional.trans ℚ
    (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below)

noncomputable instance ordinaryIdeleClassNormBaseNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)) :
    NumberField (abstractFixedField ℚ (SeparableClosure ℚ) K.field) :=
  NumberField.of_module_finite ℚ (abstractFixedField ℚ (SeparableClosure ℚ) K.field)

noncomputable instance ordinaryIdeleClassNormExtensionNumberField
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    NumberField (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below) :=
  NumberField.of_module_finite ℚ
    (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below)

/-- A direct Galois witness for the actual fixed extension, for use in
quotient computations on its original finite Galois group. -/
theorem ordinaryIdeleClassNormExtensionIsGalois
    (K : FiniteAbstractField (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsGalois (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below) :=
  abstractRelativeFixedField_isGalois ℚ (SeparableClosure ℚ)
    K.field L.field L.below L.normal

noncomputable instance ordinaryIdeleClassNormExtensionIsAbelianGalois
    (K : FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (L : FiniteAbelianSubextension K.field) :
    IsAbelianGalois
      (abstractFixedField ℚ (SeparableClosure ℚ) K.field)
      (abstractRelativeFixedField ℚ (SeparableClosure ℚ) L.below) :=
  finiteAbelianSubextensionAbstractRelativeFixedFieldIsAbelianGalois L

end GlobalClassFields
end GlobalClassFieldTheory
