/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.PrimePowerRoots
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Data.Nat.Totient

/-!
# Finiteness of prime-power roots in mixed-characteristic discrete valuation fields

Roots of unity belong to the valuation ring. The cyclotomic valuation bound gives a
single exponent annihilating every root of prime-power order, so they form a finite set.
-/

namespace ValuationTheory.DiscreteValuationField

universe u v

variable {K : Type u} [Field K]

/-- Every root of unity of positive order lies in the valuation ring. -/
theorem DVF.root_mem_valuationSubring (F : DVF.{u, v} K)
    {n : ℕ} (hn : n ≠ 0) {ζ : K} (hζ : ζ ^ n = 1) :
    ζ ∈ F.valuation.valuationSubring := by
  apply (F.mem_valuationSubring_iff ζ).mpr
  apply le_of_eq
  apply (pow_eq_one_iff_of_nonneg (show 0 ≤ F.valuation ζ from zero_le) hn).mp
  rw [← map_pow, hζ, map_one]

/-- The totient of a positive prime power bounds its exponent. -/
theorem primePower_exponent_le_totient {p : ℕ} (hp : p.Prime) (n : ℕ) :
    n + 1 ≤ Nat.totient (p ^ (n + 1)) := by
  rw [Nat.totient_prime_pow_succ hp]
  exact (Nat.succ_le_of_lt (Nat.lt_pow_self hp.one_lt)).trans
    (Nat.le_mul_of_pos_right _ (Nat.sub_pos_of_lt hp.one_lt))

section ValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]

/-- A single exponent, determined by the ramification valuation, annihilates
every prime-power root of unity in a mixed-characteristic DVR. -/
theorem primePower_pow_eq_one_of_exists (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p]
    {ζ : R} (hζ : ∃ n : ℕ, ζ ^ (p ^ n) = 1) :
    ζ ^ (p ^ (IsDiscreteValuationRing.addVal R (p : R)).toNat) = 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨n, hn⟩ := hζ
  obtain ⟨k, _hkn, hk⟩ :=
    (Nat.dvd_prime_pow hp).mp (orderOf_dvd_of_pow_eq_one hn)
  have hprim : IsPrimitiveRoot ζ (p ^ k) := IsPrimitiveRoot.iff_orderOf.mpr hk
  have hkbound : k ≤ (IsDiscreteValuationRing.addVal R (p : R)).toNat := by
    cases k with
    | zero => exact Nat.zero_le _
    | succ k =>
      have hfinite : IsDiscreteValuationRing.addVal R (p : R) ≠ ⊤ :=
        fun h => hp.ne_zero (Nat.cast_eq_zero.mp
          (IsDiscreteValuationRing.addVal_eq_top_iff.mp h))
      have hbound := ENat.toNat_le_toNat
        (primePower_totient_le_addVal p k hprim) hfinite
      rw [ENat.toNat_natCast] at hbound
      exact (primePower_exponent_le_totient hp k).trans hbound
  exact (hprim.pow_eq_one_iff_dvd _).mpr (Nat.pow_dvd_pow p hkbound)

/-- The prime-power roots in a mixed-characteristic DVR form a finite set. -/
theorem finite_primePowerRoots (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p] :
    Set.Finite {ζ : R | ∃ n : ℕ, ζ ^ (p ^ n) = 1} := by
  classical
  have hp : p.Prime := Fact.out
  apply (Polynomial.nthRootsFinset
    (p ^ (IsDiscreteValuationRing.addVal R (p : R)).toNat) (1 : R)).finite_toSet.subset
  intro ζ hζ
  exact (Polynomial.mem_nthRootsFinset (pow_pos hp.pos _) (1 : R)).mpr
    (primePower_pow_eq_one_of_exists p hζ)

end ValuationRing

/-- In mixed characteristic, a discrete valuation alone forces the prime-power
roots of unity in the field to form a finite set. -/
theorem DVF.finite_primePowerRoots [CharZero K] (F : DVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP F.residueField p] :
    Set.Finite {ζ : K | ∃ n : ℕ, ζ ^ (p ^ n) = 1} := by
  have : IsDiscreteValuationRing F.valuationSubring := F.valuationSubring_isDiscreteValuationRing
  have hfinite := ValuationTheory.DiscreteValuationField.finite_primePowerRoots
    (R := F.valuationSubring) p
  apply (hfinite.image (fun ζ : F.valuationSubring => (ζ : K))).subset
  intro ζ hζ
  obtain ⟨n, hn⟩ := hζ
  have hp : p.Prime := Fact.out
  let x : F.valuationSubring := ⟨ζ, F.root_mem_valuationSubring (pow_ne_zero n hp.ne_zero) hn⟩
  refine ⟨x, ⟨n, ?_⟩, rfl⟩
  apply Subtype.ext
  exact hn

end ValuationTheory.DiscreteValuationField
