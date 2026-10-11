/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLog
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitPadicPow
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMapContinuous
import Nyll.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitPadicContinuity
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous

/-!
# P-adic linearity of the actual principal-unit logarithm

Both scalar actions and their continuity are supplied by the preceding
constructions. Density of natural exponents upgrades additivity of the
logarithm to linearity over the p-adic integers.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- The logarithm takes a p-adic power to multiplication by that p-adic scalar. -/
theorem principalUnitLogOfMixedChar_padicPow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (a : ℤ_[p])
    (x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    (principalUnitLogOfMixedChar v p (principalUnitPadicPowOfMixedChar v p a x)).toAdd =
      padicIntToFieldOfMixedChar v p a * (principalUnitLogOfMixedChar v p x).toAdd := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1)) := principalUnitPadicModuleOfMixedChar v p
  let : Algebra ℤ_[p] K := (padicIntToFieldOfMixedChar v p).toAlgebra
  have : ContinuousSMul ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1)) :=
    principalUnitPadicContinuousSMul (K := K) p
      (hres := by change CharP (IsLocalRing.ResidueField v.valuationSubring) p; infer_instance)
  have : ContinuousSMul ℤ_[p] K := by
    refine ⟨?_⟩
    change Continuous fun z : ℤ_[p] × K => padicIntToFieldOfMixedChar v p z.1 * z.2
    exact ((continuous_padicIntToFieldOfMixedChar v p).comp continuous_fst).mul continuous_snd
  have hlog : Continuous (principalUnitLogOfMixedChar v p).toAdditiveLeft :=
    continuous_principalUnitLogOfMixedChar v p
  change (principalUnitLogOfMixedChar v p).toAdditiveLeft (a • Additive.ofMul x) =
    a • (principalUnitLogOfMixedChar v p).toAdditiveLeft (Additive.ofMul x)
  exact map_padicInt_smul_of_continuous (principalUnitLogOfMixedChar v p).toAdditiveLeft
    hlog a (Additive.ofMul x)

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
