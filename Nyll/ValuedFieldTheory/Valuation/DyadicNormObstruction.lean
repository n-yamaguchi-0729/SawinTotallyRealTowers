/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DyadicSquareRoots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity

/-!
# Quadratic norm obstruction in dyadic Henselian fields

A nonsquare defines a quadratic norm form whose values do not all lie in
the two square classes killed by adjoining its square root. The proof
normalizes the valuation, minimizes within a unit square class, and then
constructs a norm at the sharp Hensel boundary.
-/

namespace ValuationTheory

private theorem valuation_one_add_eq_one_of_one_sub_sq_value
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (b : K) (hb : v b ≤ 1)
    (hval : v (1 - b ^ 2) = 1) : v (1 + b) = 1 := by
  have hplus : v (1 + b) ≤ 1 := v.map_add_le (le_of_eq v.map_one) hb
  have hminus : v (1 - b) ≤ 1 := v.map_sub_le (le_of_eq v.map_one) hb
  apply le_antisymm hplus
  calc
    1 = v ((1 - b) * (1 + b)) := by
      rw [show (1 - b) * (1 + b) = 1 - b ^ 2 by ring, hval]
    _ = v (1 - b) * v (1 + b) := v.map_mul _ _
    _ ≤ 1 * v (1 + b) := mul_le_mul' hminus le_rfl
    _ = v (1 + b) := one_mul _

/-- Minimality within a nonsquare unit class forces the dyadic Hensel bound
to be attained if the norm of 1 + sqrt(a) lies in either allowed square class. -/
theorem valuation_sub_one_eq_two_sq_of_minimal_squareClass
    {K : Type*} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (h2 : v (2 : K) < 1) (a : K) (ha : v a = 1) (hns : ¬ IsSquare a)
    (hmin : ∀ c : Kˣ, v (c : K) = 1 →
      v (a - 1) ≤ v (a * (c : K) ^ 2 - 1))
    (hnorm : IsSquare (1 - a) ∨ IsSquare ((1 - a) / a)) :
    v (a - 1) = v (2 : K) ^ 2 := by
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [ha]; exact one_ne_zero)
  have htwo : 0 < v (2 : K) := lt_of_le_of_ne zero_le
    (Ne.symm ((Valuation.ne_zero_iff v).mpr (by norm_num)))
  have hbound : v (2 : K) ^ 2 ≤ v (a - 1) := by
    apply le_of_not_gt
    intro hsmall
    obtain ⟨b, hb⟩ := exists_sq_eq_of_valuation_sub_one_lt_two_sq v a hsmall
    exact hns ⟨b, by rw [← hb, pow_two]⟩
  have hle : v (a - 1) ≤ 1 := v.map_sub_le ha.le v.map_one.le
  by_contra hne
  have hbig : v (2 : K) ^ 2 < v (a - 1) := lt_of_le_of_ne hbound (fun h => hne h.symm)
  have hbetter (b : K) (hb : v b ^ 2 = v (a - 1)) :
      v (2 : K) * v b < v (a - 1) := by
    have hb2 : v (2 : K) < v b :=
      (pow_lt_pow_iff_left₀ zero_le zero_le (by decide : 2 ≠ 0)).mp
        (by simpa only [hb] using hbig)
    rw [← hb, pow_two]
    exact mul_lt_mul_of_pos_right hb2 (htwo.trans hb2)
  rcases hnorm with ⟨b, hb⟩ | ⟨b, hb⟩
  · rw [← pow_two] at hb
    have hbval : v b ^ 2 = v (a - 1) := by
      rw [← map_pow, ← hb, v.map_sub_swap]
    have hbone : v b ≤ 1 :=
      (pow_le_one_iff_of_nonneg zero_le (by decide : 2 ≠ 0)).mp (hbval.trans_le hle)
    have hminus : v (1 - b ^ 2) = 1 := by rw [← hb, sub_sub_cancel, ha]
    have hcval := valuation_one_add_eq_one_of_one_sub_sq_value v b hbone hminus
    have hc0 : 1 + b ≠ 0 := (Valuation.ne_zero_iff v).mp
      (by rw [hcval]; exact one_ne_zero)
    let c : Kˣ := Units.mk0 (1 + b) hc0
    have hcinv : v ((c⁻¹ : Kˣ) : K) = 1 := by
      change v ((1 + b)⁻¹) = 1
      rw [map_inv₀, hcval, inv_one]
    have hformula : a * (((c⁻¹ : Kˣ) : K)) ^ 2 - 1 = -(2 * b) / (1 + b) := by
      change a * ((1 + b)⁻¹) ^ 2 - 1 = -(2 * b) / (1 + b)
      have haexpr : a = 1 - b ^ 2 := by linear_combination -hb
      rw [haexpr]
      field_simp
      ring
    have hsmall : v (a * (((c⁻¹ : Kˣ) : K)) ^ 2 - 1) < v (a - 1) := by
      rw [hformula, v.map_div, v.map_neg, v.map_mul, hcval, div_one]
      exact hbetter b hbval
    exact (not_lt_of_ge (hmin c⁻¹ hcinv)) hsmall
  · rw [← pow_two] at hb
    have hbval : v b ^ 2 = v (a - 1) := by
      rw [← map_pow, ← hb, v.map_div, ha, div_one, v.map_sub_swap]
    have hbone : v b ≤ 1 :=
      (pow_le_one_iff_of_nonneg zero_le (by decide : 2 ≠ 0)).mp (hbval.trans_le hle)
    have hsum : 1 + b ^ 2 = a⁻¹ := by
      rw [← hb]
      field_simp
      ring
    have hsumval : v (1 + b ^ 2) = 1 := by rw [hsum, map_inv₀, ha, inv_one]
    have hminus : v (1 - b ^ 2) = 1 := by
      rw [show 1 - b ^ 2 = 2 - (1 + b ^ 2) by ring,
        v.map_sub_eq_of_lt_right (by rw [hsumval]; exact h2), hsumval]
    have hcval := valuation_one_add_eq_one_of_one_sub_sq_value v b hbone hminus
    have hc0 : 1 + b ≠ 0 := (Valuation.ne_zero_iff v).mp
      (by rw [hcval]; exact one_ne_zero)
    let c : Kˣ := Units.mk0 (1 + b) hc0
    have hformula : a * (c : K) ^ 2 - 1 = 2 * a * b := by
      change a * (1 + b) ^ 2 - 1 = 2 * a * b
      field_simp at hb
      linear_combination -hb
    have hsmall : v (a * (c : K) ^ 2 - 1) < v (a - 1) := by
      rw [hformula, v.map_mul, v.map_mul, ha, mul_one]
      exact hbetter b hbval
    exact (not_lt_of_ge (hmin c hcval)) hsmall



/-- At the dyadic Hensel boundary, a uniformizer supplies a quadratic norm
outside both possible square classes. -/
theorem exists_quadraticForm_outside_squareClasses_of_boundary
    {K : Type*} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (h2 : v (2 : K) < 1) (a π : K) (ha : v a = 1)
    (hπ : v π = WithZero.exp (-1 : ℤ))
    (heq : v (a - 1) = v (2 : K) ^ 2) :
    ∃ x y : K, ¬ IsSquare (x ^ 2 - a * y ^ 2) ∧
      ¬ IsSquare ((x ^ 2 - a * y ^ 2) / a) := by
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [ha]; exact one_ne_zero)
  have htwone : v (2 : K) ≠ 0 := (Valuation.ne_zero_iff v).mpr (by norm_num)
  have hfour : v (4 : K) = v (2 : K) ^ 2 := by
    rw [show (4 : K) = 2 ^ 2 by norm_num, map_pow]
  let u : K := (a - 1) / 4
  have hu : v u = 1 := by
    change v ((a - 1) / 4) = 1
    rw [v.map_div, hfour, heq, div_self (pow_ne_zero 2 htwone)]
  have haexpr : a = 1 + 4 * u := by
    dsimp only [u]
    field_simp
    ring
  have hπpos : 0 < v π := lt_of_le_of_ne zero_le (Ne.symm (by
    rw [hπ]
    exact WithZero.exp_ne_zero))
  have hπsmall : v π < 1 := by
    rw [hπ]
    exact WithZero.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)
  have hπsq : v π ^ 2 < v π := by
    rw [pow_two]
    calc
      v π * v π < v π * 1 := mul_lt_mul_of_pos_left hπsmall hπpos
      _ = v π := mul_one _
  have htwopi : v (2 : K) ≤ v π := by
    rw [hπ]
    have hdisc {w : WithZero (Multiplicative ℤ)} (hw0 : w ≠ 0) (hwlt : w < 1) :
        w ≤ WithZero.exp (-1 : ℤ) := by
      lift w to Multiplicative ℤ using hw0
      have hz : w < 1 := WithZero.coe_lt_coe.mp hwlt
      apply WithZero.coe_le_coe.mpr
      change Multiplicative.toAdd w < 0 at hz
      change Multiplicative.toAdd w ≤ -1
      omega
    exact hdisc htwone h2
  have h4small : v (4 : K) < v π := by
    rw [hfour]
    exact (pow_le_pow_left₀ zero_le htwopi 2).trans_lt hπsq
  have hupi : v (u * π ^ 2) < v π := by
    rw [v.map_mul, map_pow, hu, one_mul]
    exact hπsq
  have h4u : v (4 * u) < v π := by
    rw [v.map_mul, hu, mul_one]
    exact h4small
  let c : K := 1 + π - u * π ^ 2
  have hc : v (c - 1) = WithZero.exp (-1 : ℤ) := by
    rw [show c - 1 = π - u * π ^ 2 by dsimp only [c]; ring,
      v.map_sub_eq_of_lt_left hupi, hπ]
  have hca : v (c - a) = v π := by
    have hsmall : v (u * π ^ 2 + 4 * u) < v π := v.map_add_lt hupi h4u
    rw [show c - a = π - (u * π ^ 2 + 4 * u) by dsimp only [c]; rw [haexpr]; ring,
      v.map_sub_eq_of_lt_left hsmall]
  have hcdiv : v (c / a - 1) = WithZero.exp (-1 : ℤ) := by
    rw [show c / a - 1 = (c - a) / a by field_simp,
      v.map_div, hca, ha, div_one, hπ]
  have hformula : (1 + π / 2) ^ 2 - a * (π / 2) ^ 2 = c := by
    dsimp only [c, u]
    field_simp
    ring
  refine ⟨1 + π / 2, π / 2, ?_, ?_⟩
  · rw [hformula]
    exact not_isSquare_of_valuation_sub_one_eq_exp_neg_one v h2 hc
  · rw [hformula]
    exact not_isSquare_of_valuation_sub_one_eq_exp_neg_one v h2 hcdiv


/-- A nonsquare unit in a Henselian dyadic field has a quadratic norm outside
the two square classes that become squares in the quadratic extension. -/
theorem exists_quadraticForm_outside_squareClasses_of_unit
    {K : Type*} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (h2 : v (2 : K) < 1) (a π : K) (ha : v a = 1)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (hns : ¬ IsSquare a) :
    ∃ x y : K, ¬ IsSquare (x ^ 2 - a * y ^ 2) ∧
      ¬ IsSquare ((x ^ 2 - a * y ^ 2) / a) := by
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [ha]; exact one_ne_zero)
  let aunit : Kˣ := Units.mk0 a ha0
  obtain ⟨c, hc, hminimal⟩ := exists_minimal_valuation_squareClass_difference v aunit hns
  let a' : K := a * (c : K) ^ 2
  have hc0 : (c : K) ≠ 0 := Units.ne_zero c
  have ha' : v a' = 1 := by
    dsimp only [a']
    rw [v.map_mul, map_pow, ha, hc, one_pow, mul_one]
  have hns' : ¬ IsSquare a' := by
    intro hs
    apply hns
    have hdiv := hs.div (IsSquare.sq (c : K))
    have hcancel : a' / (c : K) ^ 2 = a := by
      dsimp only [a']
      exact mul_div_cancel_right₀ a (pow_ne_zero 2 hc0)
    exact hcancel ▸ hdiv
  have hmin' (d : Kˣ) (hd : v (d : K) = 1) :
      v (a' - 1) ≤ v (a' * (d : K) ^ 2 - 1) := by
    have hcd : v ((c * d : Kˣ) : K) = 1 := by
      rw [Units.val_mul, v.map_mul, hc, hd, mul_one]
    have hm := hminimal (c * d) hcd
    change v (a * (c : K) ^ 2 - 1) ≤ v (a * ((c : K) * (d : K)) ^ 2 - 1) at hm
    simpa only [mul_pow, mul_assoc, a'] using hm
  by_contra hnone
  have hnorm (x y : K) :
      IsSquare (x ^ 2 - a * y ^ 2) ∨ IsSquare ((x ^ 2 - a * y ^ 2) / a) := by
    by_cases h : IsSquare (x ^ 2 - a * y ^ 2)
    · exact Or.inl h
    · right
      by_contra hdiv
      exact hnone ⟨x, y, h, hdiv⟩
  have hnorm' (x y : K) :
      IsSquare (x ^ 2 - a' * y ^ 2) ∨ IsSquare ((x ^ 2 - a' * y ^ 2) / a') := by
    have heq : x ^ 2 - a * ((c : K) * y) ^ 2 = x ^ 2 - a' * y ^ 2 := by
      dsimp only [a']
      ring
    rcases hnorm x ((c : K) * y) with h | h
    · exact Or.inl (heq ▸ h)
    · right
      rw [heq] at h
      have hd := h.div (IsSquare.sq (c : K))
      simpa only [div_div, a'] using hd
  have hnorm1 : IsSquare (1 - a') ∨ IsSquare ((1 - a') / a') := by
    simpa only [one_pow, mul_one] using hnorm' 1 1
  have hboundary := valuation_sub_one_eq_two_sq_of_minimal_squareClass
    v h2 a' ha' hns' hmin' hnorm1
  obtain ⟨x, y, hx, hy⟩ := exists_quadraticForm_outside_squareClasses_of_boundary
    v h2 a' π ha' hπ hboundary
  exact (hnorm' x y).elim hx hy



theorem not_isSquare_of_valuation_eq_exp_odd
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (a : K) (n : ℤ) (hn : Odd n) (ha : v a = WithZero.exp n) :
    ¬ IsSquare a := by
  rintro ⟨b, rfl⟩
  have hb : v b ≠ 0 := by
    intro hz
    rw [v.map_mul, hz, zero_mul] at ha
    exact WithZero.exp_ne_zero ha.symm
  rw [v.map_mul, ← WithZero.exp_log hb, ← WithZero.exp_add] at ha
  have hlog := WithZero.exp_inj.mp ha
  obtain ⟨k, hk⟩ := hn
  omega


/-- The ramified normalized square class already gives the required norm at (1,1). -/
theorem exists_quadraticForm_outside_squareClasses_of_uniformizer_value
    {K : Type*} [Field K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    (h2 : v (2 : K) < 1) (a : K) (ha : v a = WithZero.exp (-1 : ℤ)) :
    ∃ x y : K, ¬ IsSquare (x ^ 2 - a * y ^ 2) ∧
      ¬ IsSquare ((x ^ 2 - a * y ^ 2) / a) := by
  have ha1 : v a < 1 := by
    rw [ha]
    exact WithZero.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)
  have hdiff : v ((1 - a) - 1) = WithZero.exp (-1 : ℤ) := by
    rw [show (1 - a) - 1 = -a by ring, v.map_neg, ha]
  have hval : v (1 - a) = 1 := by
    rw [v.map_sub_eq_of_lt_left (by simpa only [v.map_one] using ha1), v.map_one]
  have hdiv : v ((1 - a) / a) = WithZero.exp (1 : ℤ) := by
    rw [v.map_div, hval, ha, one_div, ← WithZero.exp_neg]
    rfl
  refine ⟨1, 1, ?_, ?_⟩
  · simp only [one_pow, mul_one]
    exact not_isSquare_of_valuation_sub_one_eq_exp_neg_one v h2 hdiff
  · simp only [one_pow, mul_one]
    exact not_isSquare_of_valuation_eq_exp_odd v ((1 - a) / a) 1 (by decide) hdiv

/-- Every nontrivial quadratic square class over a Henselian dyadic discretely valued
field has a norm which stays outside the two classes killed in the extension. -/
theorem exists_quadraticForm_outside_squareClasses
    {K : Type*} [Field K] [CharZero K]
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (h2 : v (2 : K) < 1) (a π : K)
    (hπ : v π = WithZero.exp (-1 : ℤ)) (hns : ¬ IsSquare a) :
    ∃ x y : K, ¬ IsSquare (x ^ 2 - a * y ^ 2) ∧
      ¬ IsSquare ((x ^ 2 - a * y ^ 2) / a) := by
  have ha0 : a ≠ 0 := by
    intro hz
    apply hns
    rw [hz]
    exact ⟨0, (zero_mul 0).symm⟩
  have hπ0 : π ≠ 0 := (Valuation.ne_zero_iff v).mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  let k : ℤ := WithZero.log (v a)
  let n : ℤ := (k + 1) / 2
  let c : K := π ^ n
  let a' : K := a * c ^ 2
  have hc0 : c ≠ 0 := zpow_ne_zero n hπ0
  have hc : v c = WithZero.exp (-n) := by
    dsimp only [c]
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul]
    congr 1
    simp only [zsmul_eq_mul, mul_neg, mul_one, Int.cast_id]
  have hak : v a = WithZero.exp k := (WithZero.exp_log ((Valuation.ne_zero_iff v).mpr ha0)).symm
  have ha' : v a' = WithZero.exp (k - 2 * n) := by
    dsimp only [a']
    rw [v.map_mul, map_pow, hak, hc, pow_two, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1
    ring
  have hns' : ¬ IsSquare a' := by
    intro hs
    have hdiv := hs.div (IsSquare.sq c)
    have heq : a' / c ^ 2 = a := mul_div_cancel_right₀ a (pow_ne_zero 2 hc0)
    exact hns (heq ▸ hdiv)
  have hnormalized : k - 2 * n = 0 ∨ k - 2 * n = -1 := by
    dsimp only [n]
    omega
  have hnorm : ∃ x y : K, ¬ IsSquare (x ^ 2 - a' * y ^ 2) ∧
      ¬ IsSquare ((x ^ 2 - a' * y ^ 2) / a') := by
    rcases hnormalized with hu | hram
    · apply exists_quadraticForm_outside_squareClasses_of_unit v h2 a' π _ hπ hns'
      rw [ha', hu, WithZero.exp_zero]
    · exact exists_quadraticForm_outside_squareClasses_of_uniformizer_value v h2 a'
        (ha'.trans (congrArg WithZero.exp hram))
  obtain ⟨x, y, hx, hy⟩ := hnorm
  have heq : x ^ 2 - a * (c * y) ^ 2 = x ^ 2 - a' * y ^ 2 := by
    dsimp only [a']
    ring
  refine ⟨x, c * y, heq.symm ▸ hx, ?_⟩
  intro hs
  apply hy
  rw [heq] at hs
  have hd := hs.div (IsSquare.sq c)
  simpa only [div_div, a'] using hd

end ValuationTheory
