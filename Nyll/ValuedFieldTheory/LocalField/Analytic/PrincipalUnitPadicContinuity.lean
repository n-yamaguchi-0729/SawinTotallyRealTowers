/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitValuationTopology
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.ResidueCharPrincipalUnitModule

/-!
# Continuity of the principal-unit p-adic action for the actual valuation
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
variable [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
  (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))]

open CompleteDVF.higherPrincipalUnitGroup

/-- The actual principal-unit p-adic action is continuous in the valuation topology. -/
theorem principalUnitPadicContinuousSMul (p : ℕ) [Fact p.Prime]
    [hres : CharP (completeDVFOfWithZeroValuation
      (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))).residueField p] :
    @ContinuousSMul ℤ_[p]
      (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation
        (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))) 1))
      (principalUnitPadicModuleOfResidueChar (completeDVFOfWithZeroValuation
        (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))) p).toSMul
      inferInstance inferInstance := by
  let F := completeDVFOfWithZeroValuation
    (Valued.v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
  let : Module ℤ_[p] (PrincipalUnitProdiscreteLimit F) :=
    PrincipalUnitProdiscreteLimit.padicModuleOfResidueChar F p
  have : ContinuousSMul ℤ_[p] (PrincipalUnitProdiscreteLimit F) :=
    PrincipalUnitProdiscreteLimit.padicContinuousSMulOfResidueChar F p
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    principalUnitPadicModuleOfResidueChar F p
  let e : Additive (CompleteDVF.higherPrincipalUnitGroup F 1) ≃ₜ+
      PrincipalUnitProdiscreteLimit F :=
    (principalUnitAdicContinuousAddEquiv (K := K)).symm.trans
      (adicPrincipalUnitsContinuousAddEquivProdiscreteLimit F)
  refine ⟨?_⟩
  have hpair : Continuous fun z : ℤ_[p] ×
      Additive (CompleteDVF.higherPrincipalUnitGroup F 1) => (z.1, e z.2) :=
    continuous_fst.prodMk (e.continuous.comp continuous_snd)
  exact e.continuous_symm.comp (continuous_smul.comp hpair)

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
