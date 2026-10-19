/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.OutsideIntegralInduced.LocalInduction.Spine
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.Valuation
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization

/-!
# Integral local induced modules

This file identifies the product of valuation-ring unit groups over the
extensions of a finite place with the corresponding induced module.
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

/-- The decomposition-group action on the units of the intrinsic integer
ring of the chosen localization. -/
@[reducible]
noncomputable def decompositionGroupLocalizedIntegerUnitsAction :
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
    MulDistribMulAction
      (absoluteValueDecompositionGroup K w.1)
      𝒪[LocalizedCompletion vK w]ˣ := by
  intro hBaseAlgebra hBaseSMul hCompletionAlgebra hBaseValued hBaseRel
    hLocalValued hLocalRel hIntegerAlgebra hExtension hClosure
  let hGaloisAction : MulDistribMulAction
      (Gal(LocalizedCompletion vK w / vK.Completion))
      𝒪[LocalizedCompletion vK w]ˣ :=
    galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure
      vK.Completion (LocalizedCompletion vK w)
  exact
    MulDistribMulAction.compHom
      𝒪[LocalizedCompletion vK w]ˣ
      (decompositionGroupEquivAlgebraicLocalizationAut
        vK hvK w).toMonoidHom


end IntegralInduction
