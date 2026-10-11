/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.RingHom

/-!
# The map from p-adic integers to a complete valuation ring

Reduction modulo `p^n` maps to reduction modulo the `n`th maximal-ideal power.
Adic completeness lifts these compatible maps to the actual valuation ring.
Neither characteristic zero nor finiteness of the residue field is required.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K]

private noncomputable def zmodToMaximalIdealQuotient
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (n : ℕ) :
    ZMod (p ^ n) →+* v.valuationSubring ⧸ (IsLocalRing.maximalIdeal v.valuationSubring) ^ n := by
  have hp : (p : v.valuationSubring) ∈ IsLocalRing.maximalIdeal v.valuationSubring := by
    apply (IsLocalRing.residue_eq_zero_iff (p : v.valuationSubring)).mp
    rw [map_natCast, CharP.cast_eq_zero]
  have hpn : ((p ^ n : ℕ) :
      v.valuationSubring ⧸ (IsLocalRing.maximalIdeal v.valuationSubring) ^ n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal v.valuationSubring) ^ n))]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow hp n
  exact ZMod.castHom (ringChar.dvd hpn)
    (v.valuationSubring ⧸ (IsLocalRing.maximalIdeal v.valuationSubring) ^ n)

private noncomputable def padicIntQuotientMap
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (n : ℕ) :
    ℤ_[p] →+* v.valuationSubring ⧸ (IsLocalRing.maximalIdeal v.valuationSubring) ^ n :=
  (zmodToMaximalIdealQuotient v p n).comp (PadicInt.toZModPow n)

private theorem padicIntQuotientMap_compatible
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal v.valuationSubring) h).comp
      (padicIntQuotientMap v p n) = padicIntQuotientMap v p m := by
  have hcast :
      (Ideal.Quotient.factorPow (IsLocalRing.maximalIdeal v.valuationSubring) h).comp
          (zmodToMaximalIdealQuotient v p n) =
        (zmodToMaximalIdealQuotient v p m).comp
          (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) :=
    RingHom.ext_zmod _ _
  unfold padicIntQuotientMap
  rw [← RingHom.comp_assoc, hcast, RingHom.comp_assoc,
    PadicInt.zmod_cast_comp_toZModPow m n h]

/-- The p-adic integers map to the actual complete valuation ring. -/
noncomputable def padicIntToValuationSubringOfMixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    ℤ_[p] →+* v.valuationSubring := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal v.valuationSubring) v.valuationSubring :=
    ValuationTheory.DiscreteValuationField.Valuation.isAdicComplete v
  exact IsAdicComplete.liftRingHom (IsLocalRing.maximalIdeal v.valuationSubring)
    (padicIntQuotientMap v p) (padicIntQuotientMap_compatible v p)

/-- Each coordinate of the lifted map is the canonical cast of reduction modulo `p^n`. -/
theorem padicIntToValuationSubringOfMixedChar_mod_pow
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (n : ℕ) (a : ℤ_[p]) :
    Ideal.Quotient.mk ((IsLocalRing.maximalIdeal v.valuationSubring) ^ n)
        (padicIntToValuationSubringOfMixedChar v p a) =
      ZMod.cast (PadicInt.toZModPow n a) := by
  unfold padicIntToValuationSubringOfMixedChar
  rw [IsAdicComplete.mk_liftRingHom]
  rfl

/-- The induced map from p-adic integers to the valued field. -/
noncomputable def padicIntToFieldOfMixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p] :
    ℤ_[p] →+* K :=
  v.valuationSubring.subtype.comp (padicIntToValuationSubringOfMixedChar v p)

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
