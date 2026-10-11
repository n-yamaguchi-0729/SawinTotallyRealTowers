/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.LogExpSeries.InverseEstimates
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.ResidueCharPrincipalUnitModule

/-!
# P-adic powers of actual principal units

The residue characteristic of the raw valuation supplies the characteristic
of its bundled complete-DVF residue field. Scalar multiplication is then
read multiplicatively as a p-adic power.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K]
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
variable [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]

/-- The residue-prime module expressed on the raw valuation's principal units. -/
@[instance_reducible] noncomputable def principalUnitPadicModuleOfMixedChar :
    Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1)) :=
  CompleteDVF.higherPrincipalUnitGroup.principalUnitPadicModuleOfResidueChar
    (completeDVFOfWithZeroValuation v) p
    (hres := by change CharP (IsLocalRing.ResidueField v.valuationSubring) p; infer_instance)

/-- A p-adic exponent acts on the actual multiplicative principal-unit group. -/
noncomputable def principalUnitPadicPowOfMixedChar (a : ℤ_[p])
    (x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1 :=
  Additive.toMul ((principalUnitPadicModuleOfMixedChar v p).toSMul.smul a (Additive.ofMul x))

/-- Natural p-adic exponents agree with the original group powers. -/
theorem principalUnitPadicPowOfMixedChar_natCast (n : ℕ)
    (x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    principalUnitPadicPowOfMixedChar v p (n : ℤ_[p]) x = x ^ n := by
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1)) := principalUnitPadicModuleOfMixedChar v p
  change Additive.toMul ((n : ℤ_[p]) • Additive.ofMul x) = x ^ n
  rw [Nat.cast_smul_eq_nsmul]
  rfl

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
