/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Reduced
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Cyclotomic valuation bounds in discrete valuation rings

Evaluating the prime-power cyclotomic polynomial at one gives the valuation formula.
In residue characteristic `p`, a `p`-power root reduces to one, giving the positive
valuation needed to bound the cyclotomic degree.
-/

namespace ValuationTheory.DiscreteValuationField

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The ramification valuation is the cyclotomic degree times the valuation of
the difference between a primitive prime-power root and one. -/
theorem addVal_prime_eq_totient_nsmul (p n : ℕ) [Fact p.Prime]
    {ζ : R} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    IsDiscreteValuationRing.addVal R (p : R) =
      Nat.totient (p ^ (n + 1)) • IsDiscreteValuationRing.addVal R (ζ - 1) := by
  classical
  have hp : p.Prime := Fact.out
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.ne_zero⟩
  have hprod : (p : R) = ∏ ξ ∈ primitiveRoots (p ^ (n + 1)) R, (1 - ξ) := by
    rw [← Polynomial.eval_one_cyclotomic_prime_pow n,
      Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ]
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  have hval (s : Finset R) :
      IsDiscreteValuationRing.addVal R (∏ ξ ∈ s, (1 - ξ)) =
        ∑ ξ ∈ s, IsDiscreteValuationRing.addVal R (1 - ξ) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty, IsDiscreteValuationRing.addVal_one]
    | @insert ξ s hξ ih =>
      rw [Finset.prod_insert hξ, IsDiscreteValuationRing.addVal_mul, ih,
        Finset.sum_insert hξ]
  rw [hprod, hval]
  calc
    ∑ ξ ∈ primitiveRoots (p ^ (n + 1)) R,
        IsDiscreteValuationRing.addVal R (1 - ξ) =
        ∑ ξ ∈ primitiveRoots (p ^ (n + 1)) R,
          IsDiscreteValuationRing.addVal R (ζ - 1) := by
      apply Finset.sum_congr rfl
      intro ξ hξ
      obtain ⟨j, hj, hjcop, rfl⟩ :=
        hζ.isPrimitiveRoot_iff.mp (isPrimitiveRoot_of_mem_primitiveRoots hξ)
      rw [AddValuation.map_sub_swap]
      exact (IsDiscreteValuationRing.addVal_eq_iff_associated
        (ζ ^ j - 1) (ζ - 1)).mpr
          (hζ.associated_sub_one_pow_sub_one_of_coprime hjcop).symm
    _ = Nat.totient (p ^ (n + 1)) • IsDiscreteValuationRing.addVal R (ζ - 1) := by
      rw [Finset.sum_const, hζ.card_primitiveRoots]

/-- In residue characteristic `p`, the existence of a primitive `p^(n+1)`-th
root forces its cyclotomic degree to be at most the ramification valuation. -/
theorem primePower_totient_le_addVal (p n : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField R) p]
    {ζ : R} (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    (Nat.totient (p ^ (n + 1)) : ℕ∞) ≤ IsDiscreteValuationRing.addVal R (p : R) := by
  have hres : IsLocalRing.residue R ζ = 1 := by
    have hpow : (IsLocalRing.residue R ζ) ^ (p ^ (n + 1) * 1) = 1 := by
      rw [mul_one, ← map_pow, hζ.pow_eq_one, map_one]
    simpa only [pow_one] using
      (ExpChar.pow_prime_pow_mul_eq_one_iff p (n + 1) 1
        (IsLocalRing.residue R ζ)).mp hpow
  have hpos : 1 ≤ IsDiscreteValuationRing.addVal R (ζ - 1) := by
    apply Order.one_le_iff_ne_zero.mpr
    intro hzero
    have hunit : IsUnit (ζ - 1) :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.mp hzero
    apply (IsLocalRing.residue_ne_zero_iff_isUnit (ζ - 1)).mpr hunit
    rw [map_sub, hres, map_one, sub_self]
  rw [addVal_prime_eq_totient_nsmul p n hζ, nsmul_eq_mul]
  exact le_mul_of_one_le_right (zero_le : (0 : ℕ∞) ≤ Nat.totient (p ^ (n + 1))) hpos

end ValuationTheory.DiscreteValuationField
