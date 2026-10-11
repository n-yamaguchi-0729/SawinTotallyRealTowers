/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierEisenstein
import Mathlib.Algebra.Polynomial.Div
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Failure of surjectivity for powers minus the identity in a DVF

The inverse of a prime uniformizer cannot equal `x ^ n - x` for `n > 1`: its
reciprocal polynomial is Eisenstein and would otherwise have a root in the base
field. The argument does not require Henselianity or a characteristic assumption.
-/

namespace ValuationTheory.DiscreteValuationField

open Polynomial
universe u v

/-- Powers minus the identity omit an element in every discretely valued field. -/
theorem DVF.exists_not_pow_sub
    {K : Type u} [Field K] (base : DVF.{u, v} K)
    (n : ℕ) (hn : 1 < n) :
    ∃ a : K, ∀ x : K, x ^ n - x ≠ a := by
  let R := base.valuationSubring
  let : IsDiscreteValuationRing R := base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing R K := base.valuationSubring_isFractionRing
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let a : K := algebraMap R K π
  have ha : a ≠ 0 :=
    (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 hπ.ne_zero
  refine ⟨a⁻¹, ?_⟩
  intro x hx
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, zero_pow (by omega : n ≠ 0), sub_self] at hx
    exact (inv_ne_zero ha) hx.symm
  let f : K[X] := (artinSchreierInversePolynomial π n).map (algebraMap R K)
  have hf : Irreducible f :=
    artinSchreierInversePolynomial_map_irreducible K π hπ.prime n hn
  apply hf.not_isRoot_of_natDegree_ne_one
    (by
      rw [show f.natDegree = n from
        (natDegree_map_eq_of_injective (IsFractionRing.injective R K)
          (artinSchreierInversePolynomial π n)).trans
          (artinSchreierInversePolynomial_natDegree π n hn)]
      omega) (x := x⁻¹)
  change f.eval (x⁻¹) = 0
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hmul : a * (x ^ n - x) = 1 := by rw [hx, mul_inv_cancel₀ ha]
  have hpred : x * (x⁻¹) ^ n = (x⁻¹) ^ (n - 1) := by
    rw [← hn1, pow_succ]
    calc
      x * ((x⁻¹) ^ (n - 1) * x⁻¹) =
          (x * x⁻¹) * (x⁻¹) ^ (n - 1) := by ring
      _ = (x⁻¹) ^ (n - 1) := by rw [mul_inv_cancel₀ hx0, one_mul]
  have heq : a - a * (x⁻¹) ^ (n - 1) = (x⁻¹) ^ n := by
    calc
      a - a * (x⁻¹) ^ (n - 1) =
          (a * (x ^ n - x)) * (x⁻¹) ^ n := by
        rw [mul_sub, sub_mul, mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0,
          one_pow, mul_one, mul_assoc, hpred]
      _ = (x⁻¹) ^ n := by rw [hmul, one_mul]
  change ((artinSchreierInversePolynomial π n).map (algebraMap R K)).eval (x⁻¹) = 0
  simp only [artinSchreierInversePolynomial, Polynomial.map_sub, Polynomial.map_add,
    Polynomial.map_pow, map_X, Polynomial.map_mul, map_C, eval_sub, eval_add,
    eval_pow, eval_X, eval_mul, eval_C]
  change (x⁻¹) ^ n + a * (x⁻¹) ^ (n - 1) - a = 0
  rw [← heq]
  ring

end ValuationTheory.DiscreteValuationField
