/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.Tactic.Ring

/-!
# Splitting an Artin--Schreier polynomial from one root

In characteristic `p`, translating `X ^ p - X` by a root gives the full
splitting of `X ^ p - X - C a`. This source is purely algebraic and places
no irreducibility, degree, normality, or valuation hypothesis on the field.
-/

noncomputable section


namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u

variable {K : Type u} [CommRing K]

/-- The Artin--Schreier polynomial with parameter `a`. -/
def artinSchreierPolynomial (p : ℕ) (a : K) : K[X] :=
  X ^ p - X - C a

/-- Its derivative is `-1`, so it is separable. -/
theorem artinSchreierPolynomial_separable
    (p : ℕ) [CharP K p] (a : K) :
    (artinSchreierPolynomial p a).Separable := by
  have hder : derivative (artinSchreierPolynomial p a) = -1 := by
    simp only [artinSchreierPolynomial, derivative_sub, derivative_X_pow,
      CharP.cast_eq_zero K p, map_zero, zero_mul, derivative_X,
      derivative_C, zero_sub, sub_zero]
  rw [separable_def']
  refine ⟨0, -1, ?_⟩
  rw [hder]
  ring

/-- Every prime-field translate of one root is again a root. -/
theorem artinSchreierPolynomial_isRoot_add_zmod
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (a α : K) (hα : α ^ p - α = a) (c : ZMod p) :
    (artinSchreierPolynomial p a).IsRoot
      (α + ZMod.castHom (m := p) dvd_rfl K c) := by
  have hc : (ZMod.castHom (m := p) dvd_rfl K c) ^ p =
      ZMod.castHom (m := p) dvd_rfl K c := by
    rw [← map_pow, ZMod.pow_card]
  change (artinSchreierPolynomial p a).eval
    (α + ZMod.castHom (m := p) dvd_rfl K c) = 0
  simp only [artinSchreierPolynomial, eval_sub, eval_pow, eval_X, eval_C,
    add_pow_char, hc]
  calc
    (α ^ p + ZMod.castHom (m := p) dvd_rfl K c) -
        (α + ZMod.castHom (m := p) dvd_rfl K c) - a = (α ^ p - α) - a := by ring
    _ = 0 := by rw [hα, sub_self]

/-- A single root generates the full splitting after prime-field translation. -/
theorem artinSchreierPolynomial_splits_of_root
    (p : ℕ) [Fact p.Prime] [CharP K p]
    (a α : K) (hα : α ^ p - α = a) :
    (artinSchreierPolynomial p a).Splits := by
  have hbase : (X ^ p - X : K[X]).Splits := by
    simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X] using
      (GaloisField.splits_zmod_X_pow_sub_X p).map
        (ZMod.castHom (m := p) dvd_rfl K)
  have htranslate : (X ^ p - X : K[X]).comp (X - C α) =
      artinSchreierPolynomial p a := by
    calc
      (X ^ p - X : K[X]).comp (X - C α) =
          (X - C α) ^ p - (X - C α) := by rw [sub_comp, pow_comp, X_comp]
      _ = X ^ p - X - C (α ^ p - α) := by
        rw [sub_pow_char, map_sub, map_pow]
        ring
      _ = artinSchreierPolynomial p a := by rw [hα]; rfl
  rw [← htranslate]
  exact hbase.comp_X_sub_C α

end ValuationTheory.DiscreteValuationField
