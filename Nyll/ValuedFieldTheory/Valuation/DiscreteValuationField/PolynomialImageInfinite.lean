/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.CharP.Frobenius
import Lean.Elab.Tactic.Omega

/-!
# Infinite additive quotients from a discrete valuation

The valuation argument underlying Proposition 2.4 of Bary-Soroker--Nguyen,
`On the embedding problem for Galois groups` (arXiv:1008.1879), specializes here
to discrete valuations. At sufficiently large values the leading term of a
monic polynomial dominates. Uniformizer powers whose value exponents are not
divisible by the degree then give infinitely many distinct additive classes.
No characteristic or completeness assumption is needed for that argument.
The final theorem applies it to the Artin--Schreier polynomial.
-/

open Polynomial
namespace ValuationTheory.DiscreteValuationField
universe u v

private theorem valuation_monic_eval_eq_of_coeff_lt
    {K : Type u} [Field K] {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (w : _root_.Valuation K Γ) (f : K[X]) (hf : f.Monic)
    (B : Γ) (hB : 1 ≤ B)
    (hcoeff : ∀ i ∈ Finset.range (f.natDegree + 1), w (f.coeff i) ≤ B)
    (x : K) (hx : B < w x) : w (f.eval x) = w x ^ f.natDegree := by
  have hx1 : 1 < w x := hB.trans_lt hx
  calc
    w (f.eval x) = w (f.coeff f.natDegree * x ^ f.natDegree) := by
      rw [Polynomial.eval_eq_sum_range]
      apply w.map_sum_eq_of_lt (Finset.mem_range.mpr (Nat.lt_succ_self _))
      intro i hi
      have hi' : i < f.natDegree := by
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_singleton] at hi
        omega
      rw [Polynomial.coeff_natDegree, hf.leadingCoeff, one_mul, map_pow, map_mul, map_pow]
      calc
        w (f.coeff i) * w x ^ i < w x * w x ^ i :=
          mul_lt_mul_of_pos_right ((hcoeff i (Finset.mem_range.mpr (by omega))).trans_lt hx)
            (pow_pos (zero_lt_one.trans hx1) i)
        _ = w x ^ (i + 1) := (pow_succ' (w x) i).symm
        _ ≤ w x ^ f.natDegree := pow_le_pow_right₀ hx1.le (by omega)
    _ = w x ^ f.natDegree := by
      rw [Polynomial.coeff_natDegree, hf.leadingCoeff, one_mul, map_pow]

private theorem valuation_eval_le_of_coeff_le
    {K : Type u} [Field K] {Γ : Type v} [LinearOrderedCommGroupWithZero Γ]
    (w : _root_.Valuation K Γ) (f : K[X])
    (B : Γ) (hB : 1 ≤ B)
    (hcoeff : ∀ i ∈ Finset.range (f.natDegree + 1), w (f.coeff i) ≤ B)
    (x : K) (hx : w x ≤ B) : w (f.eval x) ≤ B ^ (f.natDegree + 1) := by
  rw [Polynomial.eval_eq_sum_range]
  apply w.map_sum_le
  intro i hi
  have hi' : i ≤ f.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_mul, map_pow]
  calc
    w (f.coeff i) * w x ^ i ≤ B * B ^ i := mul_le_mul' (hcoeff i hi) (pow_le_pow_left₀ zero_le hx i)
    _ = B ^ (i + 1) := (pow_succ' B i).symm
    _ ≤ B ^ (f.natDegree + 1) := pow_le_pow_right₀ hB (Nat.succ_le_succ hi')

private theorem exists_coefficient_bound
    {K : Type u} [Field K] (w : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    (f : K[X]) :
    ∃ M : ℕ, ∀ i ∈ Finset.range (f.natDegree + 1),
      w (f.coeff i) ≤ WithZero.exp (M : ℤ) := by
  let M : ℕ := (Finset.range (f.natDegree + 1)).sup (fun i => (WithZero.log (w (f.coeff i))).natAbs)
  refine ⟨M, ?_⟩
  intro i hi
  apply WithZero.le_exp_of_log_le
  exact Int.le_natAbs.trans
    (by exact_mod_cast Finset.le_sup (f := fun i => (WithZero.log (w (f.coeff i))).natAbs) hi)

/-- Every monic polynomial of degree greater than one has infinitely many
pairwise distinct additive image classes over a discretely valued field. -/
theorem DVF.exists_sequence_sub_not_mem_polynomial_range
    {K : Type u} [Field K] (D : DVF.{u, v} K)
    (f : K[X]) (hf : f.Monic) (hd : 1 < f.natDegree) :
    ∃ a : ℕ → K, ∀ i j : ℕ, i ≠ j → a i - a j ∉ Set.range f.eval := by
  obtain ⟨w, _hw, _hring, π, hπ⟩ := D.exists_normalized_valuation_with_uniformizer
  obtain ⟨M, hM⟩ := exists_coefficient_bound w f
  let B : WithZero (Multiplicative ℤ) := WithZero.exp (M : ℤ)
  have hB : 1 ≤ B := WithZero.one_le_exp_iff.mpr (Int.natCast_nonneg M)
  let e (n : ℕ) : ℤ := (f.natDegree : ℤ) * ((M : ℤ) * (f.natDegree + 1) + n + 1) + 1
  let a (n : ℕ) : K := π ^ (-e n)
  have ha (n : ℕ) : w (a n) = WithZero.exp (e n) := by
    change w (π ^ (-e n)) = _
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, zsmul_eq_mul]
    congr 1
    change (-e n) * (-1 : ℤ) = e n
    ring
  have he (n : ℕ) : (M : ℤ) * (f.natDegree + 1) < e n := by
    dsimp only [e]
    have hd' : (1 : ℤ) < f.natDegree := by exact_mod_cast hd
    have hM0 : (0 : ℤ) ≤ M := Int.natCast_nonneg M
    have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have ht0 : 0 ≤ (M : ℤ) * (f.natDegree + 1) := mul_nonneg hM0 (by omega)
    have ht := mul_le_mul_of_nonneg_right hd'.le ht0
    have hn := mul_nonneg (show (0 : ℤ) ≤ f.natDegree by omega) hn0
    nlinarith
  have hnot (n : ℕ) (x : K) (hx : w x = WithZero.exp (e n)) :
      x ∉ Set.range f.eval := by
    rintro ⟨y, hy⟩
    change f.eval y = x at hy
    have hlarge : B ^ (f.natDegree + 1) < w (f.eval y) := by
      rw [hy, hx]
      change WithZero.exp (M : ℤ) ^ (f.natDegree + 1) < _
      rw [← WithZero.exp_nsmul, nsmul_eq_mul, WithZero.exp_lt_exp]
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using he n
    have hBy : B < w y := by
      by_contra hle
      exact (not_le_of_gt hlarge)
        (valuation_eval_le_of_coeff_le w f B hB hM y (le_of_not_gt hle))
    have hval : w y ^ f.natDegree = WithZero.exp (e n) :=
      (valuation_monic_eval_eq_of_coeff_lt w f hf B hB hM y hBy).symm.trans
        ((congrArg w hy).trans hx)
    have hlog := congrArg WithZero.log hval
    rw [WithZero.log_pow, WithZero.log_exp, nsmul_eq_mul] at hlog
    have hdiv : (f.natDegree : ℤ) ∣ e n := ⟨WithZero.log (w y), hlog.symm⟩
    have hdivone : (f.natDegree : ℤ) ∣ 1 := by
      have hmul : (f.natDegree : ℤ) ∣
          (f.natDegree : ℤ) * ((M : ℤ) * (f.natDegree + 1) + n + 1) := dvd_mul_right _ _
      have hsub := dvd_sub hdiv hmul
      convert hsub using 1
      dsimp only [e]
      ring
    have hnat : f.natDegree ∣ 1 := by exact_mod_cast hdivone
    exact (Nat.not_le_of_lt hd) (Nat.le_of_dvd (by decide : 0 < 1) hnat)
  have hmono : StrictMono (fun n : ℕ => w (a n)) := by
    intro i j hij
    change w (a i) < w (a j)
    rw [ha, ha, WithZero.exp_lt_exp]
    have hd0 : (0 : ℤ) < f.natDegree := by exact_mod_cast lt_trans Nat.zero_lt_one hd
    have hij' : (i : ℤ) < j := by exact_mod_cast hij
    dsimp only [e]
    nlinarith
  refine ⟨a, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hnot j (a i - a j) ((w.map_sub_eq_of_lt_right (hmono hlt)).trans (ha j))
  · exact hnot i (a i - a j) ((w.map_sub_eq_of_lt_left (hmono hgt)).trans (ha i))

/-- The quotient by the image of an additive monic polynomial of degree at
least two is infinite over every discretely valued field. -/
theorem DVF.infinite_quotient_range_of_monic_polynomial
    {K : Type u} [Field K] (D : DVF.{u, v} K)
    (f : K[X]) (hf : f.Monic) (hd : 1 < f.natDegree)
    (F : K →+ K) (hF : ∀ x : K, F x = f.eval x) :
    Infinite (K ⧸ F.range) := by
  obtain ⟨a, ha⟩ := D.exists_sequence_sub_not_mem_polynomial_range f hf hd
  apply Infinite.of_injective (fun n : ℕ => QuotientAddGroup.mk' F.range (a n))
  intro i j hij
  by_contra hne
  apply ha i j hne
  have hmem : a i - a j ∈ F.range := QuotientAddGroup.eq_iff_sub_mem.mp hij
  obtain ⟨x, hx⟩ := hmem
  exact ⟨x, (hF x).symm.trans hx⟩

/-- The Artin--Schreier quotient of a discretely valued field is infinite. -/
theorem DVF.infinite_artinSchreier_quotient
    {K : Type u} [Field K] (D : DVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Infinite (K ⧸ ((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range) := by
  let f : K[X] := X ^ p - X
  have hdeg : f.natDegree = p := by
    apply (Polynomial.natDegree_sub_eq_left_of_natDegree_lt ?_).trans
      (Polynomial.natDegree_X_pow p)
    rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow]
    exact (Fact.out : p.Prime).one_lt
  have hf : f.Monic := by
    apply (Polynomial.monic_X.pow p).sub_of_left
    rw [Polynomial.degree_X, Polynomial.degree_X_pow]
    exact_mod_cast (Fact.out : p.Prime).one_lt
  apply D.infinite_quotient_range_of_monic_polynomial f hf
    (hdeg.symm ▸ (Fact.out : p.Prime).one_lt)
  intro x
  change x ^ p - x = f.eval x
  rw [show f = X ^ p - X from rfl, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X]

end ValuationTheory.DiscreteValuationField
