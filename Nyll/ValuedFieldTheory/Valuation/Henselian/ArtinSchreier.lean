/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.NonmonicSimpleRoot
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Artin–Schreier roots in a Henselian valuation ring

In characteristic p, the maximal ideal is contained in the image of
x ↦ x^p - x. Consequently this additive image is open in the valued field.
-/

namespace ValuationTheory

open Polynomial

/-- Every element of positive valuation is an Artin–Schreier difference in
a Henselian valued field of positive characteristic. -/
theorem exists_pow_sub_eq_of_valuation_lt_one
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (p : ℕ) [Fact p.Prime] [CharP K p] (a : K) (ha : v a < 1) :
    ∃ b : K, b ^ p - b = a := by
  let R := v.valuationSubring
  have : CharP R p := CharP.subring K p v.valuationSubring.toSubring
  let a₀ : R := ⟨a, ha.le⟩
  let f : R[X] := X ^ p - X - C a₀
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hroot : f.eval 0 ∈ IsLocalRing.maximalIdeal R := by
    have ha₀ : a₀ ∈ IsLocalRing.maximalIdeal R := v.mem_maximalIdeal_iff.mpr ha
    simpa only [f, eval_sub, eval_pow, eval_X, eval_C, zero_pow hp0, sub_zero,
      zero_sub] using (IsLocalRing.maximalIdeal R).neg_mem ha₀
  have hderiv : f.derivative.eval 0 = -1 := by
    simp only [f, derivative_sub, derivative_pow, derivative_X, derivative_C,
      eval_sub, eval_mul, eval_C, CharP.cast_eq_zero R p, zero_mul,
      eval_one, sub_zero, zero_sub]
  have hunit : IsUnit (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
      (f.derivative.eval 0)) := by
    rw [hderiv, map_neg, map_one]
    exact isUnit_one.neg
  obtain ⟨b, hb, _⟩ :=
    DiscreteValuationField.exists_root_of_henselianRing_of_simpleRoot_mod
      v.valuationSubring f 0 hroot hunit
  have hbeval : b ^ p - b - a₀ = 0 := by
    simpa only [f, eval_sub, eval_pow, eval_X, eval_C] using Polynomial.IsRoot.def.mp hb
  refine ⟨(b : K), ?_⟩
  exact congrArg ((↑) : R → K) (sub_eq_zero.mp hbeval)

/-- The additive Artin–Schreier image is open in a Henselian valued field of
characteristic p. -/
theorem isOpen_artinSchreier_range
    {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
    [HenselianRing (Valued.v : Valuation K Γ).valuationSubring
      (IsLocalRing.maximalIdeal (Valued.v : Valuation K Γ).valuationSubring)]
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    IsOpen (((frobenius K p).toAddMonoidHom - AddMonoidHom.id K).range : Set K) := by
  let v : Valuation K Γ := Valued.v
  apply AddSubgroup.isOpen_of_mem_nhds (g := (0 : K))
  apply Filter.mem_of_superset ((Valued.isOpen_ball K (1 : v.ValueGroup₀)).mem_nhds ?_)
  · intro a ha
    obtain ⟨b, hb⟩ := exists_pow_sub_eq_of_valuation_lt_one v p a
      (v.restrict_lt_one_iff.mp ha)
    exact ⟨b, hb⟩
  · change v.restrict 0 < 1
    rw [map_zero]
    exact zero_lt_one

end ValuationTheory
