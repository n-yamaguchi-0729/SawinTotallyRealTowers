/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.ShrinkFiniteAbelianFields
public import Nyll.ValuedFieldTheory.LocalField.NormUnitsBaseChange
public import Nyll.ValuedFieldTheory.LocalField.NormUnits

/-!
# Norm subgroups under a small change of local base field

The field norm from an intermediate field is unchanged after re-expressing
that intermediate field over the equivalent small base field.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The norm subgroup attached to an intermediate field is carried to the
norm subgroup of the same field viewed over `Shrink K`. -/
theorem shrinkIntermediateField_normSubgroup_map
    (E : ClassFieldTheory.FiniteAbelianLocalExtension K) :
    let : Small.{0} K := nonarchimedeanLocalField_small K
    let : Algebra (Shrink.{0} K) (SeparableClosure K) :=
      shrinkSeparableClosureAlgebra K
    let : FiniteDimensional (Shrink.{0} K) (shrinkIntermediateField K E.1) :=
      shrinkIntermediateField_finiteDimensional K E
    (E.normSubgroup).map
        (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
      localNormSubgroup (Shrink.{0} K)
        (shrinkIntermediateField K E.1) := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  change (localNormSubgroup K E.1).map
      (Units.mapEquiv (Shrink.ringEquiv K).symm.toMulEquiv).toMonoidHom =
    localNormSubgroup (Shrink.{0} K)
      (shrinkIntermediateField K E.1)
  exact LocalFieldTheory.localNormSubgroup_map_ringEquiv
    (Shrink.ringEquiv K).symm
    (shrinkIntermediateFieldRingEquiv K E.1)
    (shrinkIntermediateFieldRingEquiv_commutes K E.1)

end LocalFieldTheory
