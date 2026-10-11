/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogBound
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.ValuationSubringUnits.IntegerValuation
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.LeastGreatest

/-!
# The principal-unit logarithm image has no nonzero p-divisible subgroup

The uniform lower bound on the integer valuations of logarithms gives a
least valuation among the nonzero elements of any nonzero subgroup of the
logarithm image. Dividing a least element by the residue prime strictly
decreases its valuation. Thus such a subgroup cannot be `p`-divisible.

Only the actual logarithm image is an input; its valuation bound is generated
from the mixed-characteristic logarithm theorem. No closedness, finite
generation, finite residue field, or additional scalar structure is needed.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- An additive subgroup of the actual principal-unit logarithm image is zero
if multiplication by the residue prime is surjective on that subgroup. -/
theorem addSubgroup_eq_bot_of_principalUnitLog_image_of_p_divisible
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (J : AddSubgroup K)
    (hlog : (J : Set K) ⊆
      Set.range (fun u => (principalUnitLogOfMixedChar v p u).toAdd))
    (hdiv : ∀ x : K, x ∈ J → ∃ y : K, y ∈ J ∧ p • y = x) :
    J = ⊥ := by
  obtain ⟨m, _hm, hbound⟩ := exists_principalUnitLog_denominator_min_bound v p
  let d : ℤ := ((m + 1 : ℕ) : ℤ) - (v.residueRamificationIndex p : ℤ) *
    (padicValNat p (m + 1) : ℤ)
  let val : Kˣ → ℤ := (ofWithZeroValuation v).val
  have hlower (b : Kˣ) (hb : (b : K) ∈ J) : d ≤ val b := by
    obtain ⟨u, hu⟩ := hlog hb
    change (principalUnitLogOfMixedChar v p u).toAdd = (b : K) at hu
    have hune : (principalUnitLogOfMixedChar v p u).toAdd ≠ 0 := by
      rw [hu]
      exact b.ne_zero
    have hunit : Units.mk0 (principalUnitLogOfMixedChar v p u).toAdd hune = b :=
      Units.ext hu
    have h := hbound u hune
    rw [hunit] at h
    exact h
  rw [AddSubgroup.eq_bot_iff_forall]
  intro a ha
  by_contra hane
  obtain ⟨z, ⟨b, hb, hbz⟩, hz⟩ :=
    Int.exists_least_of_bdd
      (P := fun z => ∃ b : Kˣ, (b : K) ∈ J ∧ val b = z)
      (by
        refine ⟨d, ?_⟩
        rintro z ⟨b, hb, hbz⟩
        rw [← hbz]
        exact hlower b hb)
      ⟨val (Units.mk0 a hane), Units.mk0 a hane, ha, rfl⟩
  obtain ⟨y, hy, hpy⟩ := hdiv (b : K) hb
  have hyne : y ≠ 0 := by
    intro hyzero
    apply b.ne_zero
    rw [← hpy, hyzero, nsmul_zero]
  have hp : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hproduct : Units.mk0 (p : K) hp * Units.mk0 y hyne = b := by
    apply Units.ext
    change (p : K) * y = (b : K)
    simpa only [nsmul_eq_mul] using hpy
  have hmin : val b ≤ val (Units.mk0 y hyne) := by
    rw [hbz]
    exact hz (val (Units.mk0 y hyne)) ⟨Units.mk0 y hyne, hy, rfl⟩
  have hval : val (Units.mk0 (p : K) hp) + val (Units.mk0 y hyne) = val b := by
    change (ofWithZeroValuation v).val (Units.mk0 (p : K) hp) +
      (ofWithZeroValuation v).val (Units.mk0 y hyne) = (ofWithZeroValuation v).val b
    rw [← (ofWithZeroValuation v).val_mul, hproduct]
  have hpval : 0 < val (Units.mk0 (p : K) hp) := by
    change 0 < -WithZero.log (v (p : K))
    exact neg_pos.mpr (v.log_natCast_residueChar_neg p)
  have hlt : val (Units.mk0 y hyne) < val b := by
    rw [← hval]
    exact lt_add_of_pos_left (val (Units.mk0 y hyne)) hpval
  exact (not_lt_of_ge hmin) hlt

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
