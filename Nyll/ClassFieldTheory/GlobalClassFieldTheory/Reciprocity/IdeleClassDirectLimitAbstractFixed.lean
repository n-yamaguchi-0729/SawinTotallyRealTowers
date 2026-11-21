/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFixedDescent
public import Nyll.ClassFieldTheory.Algebra.FiniteAbstractFixedField

/-!
# Standard idele classes of abstract fixed fields

The actual fixed fields of closed subgroups enter the same number-field
coefficient representation through the standard finite-field inclusion.
-/

@[expose] public section

open scoped NumberField
open LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- The standard class group of an actual finite fixed field is the fixed
part at the original closed subgroup. -/
def abstractFixedFieldIdeleClassEquivFixed
    (H : ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H)] :
    Additive (NumberField.IdeleClassGroup
      (𝓞 (abstractFixedField K (SeparableClosure K) H))
      (abstractFixedField K (SeparableClosure K) H)) ≃+
      KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation K) H :=
  (ideleClassEquivFixed K (abstractFixedField K (SeparableClosure K) H)).trans
    (AddEquiv.addSubgroupCongr
      (congrArg (KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation K))
        (closedFixingSubgroup_abstractFixedField_eq K (SeparableClosure K) H)))

/-- The closed-subgroup comparison retains the actual intermediate-field
class in the one absolute limit. -/
theorem abstractFixedFieldIdeleClassEquivFixed_coe
    (H : ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K))
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H)]
    (c : Additive (NumberField.IdeleClassGroup
      (𝓞 (abstractFixedField K (SeparableClosure K) H))
      (abstractFixedField K (SeparableClosure K) H))) :
    (abstractFixedFieldIdeleClassEquivFixed K H c).1 =
      Additive.ofMul (intermediateIdeleClassToDirectLimit K
        (abstractFixedField K (SeparableClosure K) H) (Additive.toMul c)) := rfl

/-- Extending the scalar base of the fixed field preserves its actual
number-field structure. -/
noncomputable local instance abstractRelativeFixedFieldNumberField
    {H J : ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K)}
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J)] :
    NumberField (abstractRelativeFixedField K (SeparableClosure K) hJH) := by
  change NumberField (abstractFixedField K (SeparableClosure K) J)
  infer_instance

/-- The same upper fixed field, regarded over the lower field, has the same
standard idele-class comparison. No second direct limit is used. -/
def abstractRelativeFixedFieldIdeleClassEquivFixed
    (H J : ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K))
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J)] :
    Additive (NumberField.IdeleClassGroup
      (𝓞 (abstractRelativeFixedField K (SeparableClosure K) hJH))
      (abstractRelativeFixedField K (SeparableClosure K) hJH)) ≃+
      KummerTheory.ambientFixedAddSubgroup (ideleClassRepresentation K) J :=
  abstractFixedFieldIdeleClassEquivFixed K J

end GlobalClassFieldTheory.Reciprocity
