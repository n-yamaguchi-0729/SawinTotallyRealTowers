/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitPadicPow
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.ValuationSubringUnitMap
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# P-adic exponents modulo prime powers

Reduction of a p-adic exponent modulo `p^s` changes its action on a principal
unit by an actual `p^s`-th power. The witness is constructed in the principal
unit group and then mapped into the field unit group.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K]
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
variable [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]

/-- A p-adic exponent and its natural residue modulo `p^s` differ on a
principal unit by an actual `p^s`-th power in the principal-unit group. -/
theorem exists_principalUnitPadicPow_div_natCast_eq_pow (a : ℤ_[p])
    (x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)
    (s : ℕ) :
    ∃ y : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      principalUnitPadicPowOfMixedChar v p a x /
          x ^ (PadicInt.toZModPow s a).val = y ^ (p ^ s) := by
  let n : ℕ := (PadicInt.toZModPow s a).val
  have hker : a - (n : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow s) := by
    rw [RingHom.mem_ker, map_sub, map_natCast]
    exact sub_eq_zero.mpr (ZMod.natCast_zmod_val (PadicInt.toZModPow s a)).symm
  have hdiv : (p : ℤ_[p]) ^ s ∣ a - (n : ℤ_[p]) := by
    apply Ideal.mem_span_singleton.mp
    rw [← PadicInt.ker_toZModPow]
    exact hker
  obtain ⟨c, hc⟩ := hdiv
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup
      (completeDVFOfWithZeroValuation v) 1)) := principalUnitPadicModuleOfMixedChar v p
  refine ⟨principalUnitPadicPowOfMixedChar v p c x, ?_⟩
  change Additive.toMul (a • Additive.ofMul x) / x ^ n =
    Additive.toMul (c • Additive.ofMul x) ^ (p ^ s)
  have hsmul :
      a • Additive.ofMul x - (n : ℤ_[p]) • Additive.ofMul x =
        (p ^ s : ℕ) • (c • Additive.ofMul x) := by
    rw [← sub_smul, hc, mul_smul, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  simpa only [toMul_sub, Nat.cast_smul_eq_nsmul,
    toMul_nsmul, toMul_ofMul] using
    congrArg (Additive.toMul :
      Additive (CompleteDVF.higherPrincipalUnitGroup
        (completeDVFOfWithZeroValuation v) 1) →
      CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) hsmul

/-- The same exponent reduction has an actual `p^s`-th power witness in the
field unit group, obtained by mapping the principal-unit witness. -/
theorem exists_fieldUnit_principalUnitPadicPow_div_natCast_eq_pow (a : ℤ_[p])
    (x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)
    (s : ℕ) :
    ∃ y : Kˣ,
      CompleteDVF.valuationSubringUnitsToFieldUnits (completeDVFOfWithZeroValuation v)
          (principalUnitPadicPowOfMixedChar v p a x :
            (completeDVFOfWithZeroValuation v).valuationSubringˣ) /
        (CompleteDVF.valuationSubringUnitsToFieldUnits (completeDVFOfWithZeroValuation v)
          (x : (completeDVFOfWithZeroValuation v).valuationSubringˣ)) ^
            (PadicInt.toZModPow s a).val = y ^ (p ^ s) := by
  let ι : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1 →* Kˣ :=
    (CompleteDVF.valuationSubringUnitsToFieldUnits (completeDVFOfWithZeroValuation v)).comp
      (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1).subtype
  obtain ⟨y, hy⟩ := exists_principalUnitPadicPow_div_natCast_eq_pow v p a x s
  refine ⟨ι y, ?_⟩
  change ι (principalUnitPadicPowOfMixedChar v p a x) /
    (ι x) ^ (PadicInt.toZModPow s a).val = (ι y) ^ (p ^ s)
  simpa only [_root_.map_div, _root_.map_pow] using congrArg ι hy

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
