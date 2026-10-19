/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Equiv
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Action
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic

/-!
# Inclusion of integral local induced modules

This leaf embeds the induced integer-unit module into the ordinary local
multiplicative induced block and proves injectivity.
-/



open scoped NumberField TensorProduct ValuativeRel NNReal
open NumberField IsDedekindDomain

noncomputable section

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

variable
    {K : Type} {L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

section IntegralInduction

variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
    (hvKna : IsNonarchimedean (vK : K → ℝ))
    (w : AbsoluteValueExtension vK L)

/-- Pointwise inclusion of integer units embeds the integral induced
block into the ordinary local multiplicative induced block. -/
noncomputable def inducedIntegerUnitsToLocalPlaceBlock :
    let _ : Algebra K w.1.Completion :=
      LocalInductionInternal.extensionCompletionAlgebra vK w
    let _ : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    let _ : Algebra vK.Completion w.1.Completion :=
      LocalInductionInternal.completionAlgebra vK w
    let _ : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    let _ : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    let _ : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    let _ : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    let _ : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    let _ : Valuation.HasExtension
        (ValuativeRel.valuation vK.Completion)
        (ValuativeRel.valuation (LocalizedCompletion vK w)) :=
      LocalInductionInternal.valuationHasExtension vK w hvKna
    let _ : IsIntegralClosure
        𝒪[LocalizedCompletion vK w] 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.isIntegralClosure vK w hvK hvKna
    let _ : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1) 𝒪[LocalizedCompletion vK w]ˣ :=
      decompositionGroupLocalizedIntegerUnitsAction
        (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    CyclicCohomology.InducedModule
        (B := 𝒪[LocalizedCompletion vK w]ˣ)
        (absoluteValueDecompositionGroup K w.1) →*
      LocalPlaceBlock vK hvK w := by
  intro hBaseAlgebra hBaseSMul hCompletionAlgebra hBaseValued hBaseRel
    hLocalValued hLocalRel hIntegerAlgebra hExtension hClosure hIntegerAction
  let hFieldAction : MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1) (LocalizedCompletion vK w)ˣ :=
    decompositionGroupLocalUnitsAction vK hvK w
  refine
    { toFun := fun f =>
        ⟨fun g =>
            LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
              (LocalizedCompletion vK w) (f.1 g),
          by
            intro h g
            change
              LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                    (LocalizedCompletion vK w) (f.1 (h.1 * g)) =
                h •
                  LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits
                    (LocalizedCompletion vK w) (f.1 g)
            rw [f.2 h g]
            exact
              integerUnitsToFieldUnits_galoisGroup_equivariant
                vK.Completion (LocalizedCompletion vK w)
                (decompositionGroupEquivAlgebraicLocalizationAut
                  vK hvK w h)
                (f.1 g)⟩
      map_one' := by
        apply Subtype.ext
        funext g
        rfl
      map_mul' := fun f₁ f₂ ↦ by
        apply Subtype.ext
        funext g
        rfl }

omit [NumberField K] [NumberField L] in
/-- The map from induced localized integer units to the corresponding
local-place block is injective. -/
theorem inducedIntegerUnitsToLocalPlaceBlock_injective :
    let _ : Algebra K w.1.Completion :=
      LocalInductionInternal.extensionCompletionAlgebra vK w
    let _ : SMul K w.1.Completion :=
      LocalInductionInternal.extensionCompletionSMul vK w
    let _ : Algebra vK.Completion w.1.Completion :=
      LocalInductionInternal.completionAlgebra vK w
    let _ : Valued vK.Completion ℝ≥0 :=
      LocalInductionInternal.baseValued vK hvKna
    let _ : ValuativeRel vK.Completion :=
      LocalInductionInternal.baseValuativeRel vK hvKna
    let _ : Valued (LocalizedCompletion vK w) ℝ≥0 :=
      LocalInductionInternal.localizedValued vK w hvKna
    let _ : ValuativeRel (LocalizedCompletion vK w) :=
      LocalInductionInternal.localizedValuativeRel vK w hvKna
    let _ : Algebra 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.integerAlgebra vK w hvKna
    let _ : Valuation.HasExtension
        (ValuativeRel.valuation vK.Completion)
        (ValuativeRel.valuation (LocalizedCompletion vK w)) :=
      LocalInductionInternal.valuationHasExtension vK w hvKna
    let _ : IsIntegralClosure
        𝒪[LocalizedCompletion vK w] 𝒪[vK.Completion] (LocalizedCompletion vK w) :=
      LocalInductionInternal.isIntegralClosure vK w hvK hvKna
    let _ : MulDistribMulAction
        (absoluteValueDecompositionGroup K w.1) 𝒪[LocalizedCompletion vK w]ˣ :=
      decompositionGroupLocalizedIntegerUnitsAction
        (vK := vK) (hvK := hvK) (hvKna := hvKna) (w := w)
    Function.Injective
      (inducedIntegerUnitsToLocalPlaceBlock
        (K := K) (L := L) vK hvK hvKna w) := by
  intro hBaseAlgebra hBaseSMul hCompletionAlgebra hBaseValued hBaseRel
    hLocalValued hLocalRel hIntegerAlgebra hExtension hClosure hIntegerAction f₁ f₂ h
  apply Subtype.ext
  funext g
  apply
    LocalFieldTheory.IsNonarchimedeanLocalField.integerUnitsToFieldUnits_injective
      (LocalizedCompletion vK w)
  exact congrArg
    (fun z : LocalPlaceBlock vK hvK w => z.1 g) h


end IntegralInduction
