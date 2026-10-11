/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.AbsoluteValues
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Data.Fintype.EquivFin

/-!
# Weak approximation for discrete valuations

A finite family of inequivalent discrete valuations admits simultaneous
approximation, with independently prescribed nonzero valuation radii.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

variable {K : Type*} [Field K]

noncomputable local instance (D : DVF K) : D.valuation.RankOne :=
  _root_.Valuation.IsRankOneDiscrete.rankOne D.valuation (e := 2) (by norm_num)

/-- A real absolute value inducing the ordering of a discrete valuation. -/
noncomputable def realAbsoluteValue (D : DVF K) : AbsoluteValue K ℝ where
  toFun := D.valuation.norm
  map_mul' x y := by
    simp only [_root_.Valuation.norm, map_mul, NNReal.coe_mul]
  nonneg' := D.valuation.norm_nonneg
  eq_zero' x := ⟨D.valuation.norm_eq_zero, fun hx => by
    rw [hx, _root_.Valuation.norm, map_zero, map_zero, NNReal.coe_zero]⟩
  add_le' x y := (D.valuation.norm_add_le x y).trans
    (max_le_add_of_nonneg (D.valuation.norm_nonneg x) (D.valuation.norm_nonneg y))

/-- The associated real absolute value preserves and reflects strict valuation inequalities. -/
theorem realAbsoluteValue_lt_iff (D : DVF K) (x y : K) :
    D.realAbsoluteValue x < D.realAbsoluteValue y ↔ D.valuation x < D.valuation y := by
  change (↑(_root_.Valuation.RankOne.hom D.valuation (D.valuation.restrict x)) : ℝ) <
    ↑(_root_.Valuation.RankOne.hom D.valuation (D.valuation.restrict y)) ↔ _
  rw [NNReal.coe_lt_coe, (_root_.Valuation.RankOne.strictMono D.valuation).lt_iff_lt]
  exact D.valuation.restrict_lt_iff

/-- The associated real absolute value is nontrivial, as witnessed by a uniformizer. -/
theorem realAbsoluteValue_isNontrivial (D : DVF K) :
    D.realAbsoluteValue.IsNontrivial := by
  obtain ⟨π, hπ⟩ := D.exists_uniformizer
  refine ⟨(π : K), hπ.ne_zero, ?_⟩
  have hlt := (D.realAbsoluteValue_lt_iff (π : K) 1).mpr
    (by rw [map_one]; exact hπ.val_lt_one)
  rw [map_one] at hlt
  exact hlt.ne

/-- Associated real absolute values are equivalent exactly when the valuations are equivalent. -/
theorem realAbsoluteValue_isEquiv_iff (D E : DVF K) :
    D.realAbsoluteValue.IsEquiv E.realAbsoluteValue ↔ D.valuation.IsEquiv E.valuation := by
  constructor
  · intro h x y
    exact le_iff_le_iff_lt_iff_lt.mpr
      ((D.realAbsoluteValue_lt_iff y x).symm.trans
        (h.lt_iff_lt.trans (E.realAbsoluteValue_lt_iff y x)))
  · intro h x y
    exact le_iff_le_iff_lt_iff_lt.mpr
      ((D.realAbsoluteValue_lt_iff y x).trans
        (h.lt_iff_lt.trans (E.realAbsoluteValue_lt_iff y x).symm))

/-- Simultaneous approximation with an individual nonzero radius at each
valuation. Neither completeness nor Henselianity is required. -/
theorem exists_forall_valuation_sub_lt {ι : Type*} [Finite ι]
    (D : ι → DVF K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (a b : ι → K) (hb : ∀ i, b i ≠ 0) :
    ∃ x : K, ∀ i, (D i).valuation (x - a i) < (D i).valuation (b i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hε : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ (Finset.univ : Finset ι),
      ε ≤ (D i).realAbsoluteValue (b i) := by
    generalize (Finset.univ : Finset ι) = s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, fun i hi => (Finset.notMem_empty i hi).elim⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hpos, hε⟩ := ih
      refine ⟨min ε ((D i).realAbsoluteValue (b i)),
        lt_min hpos ((D i).realAbsoluteValue.pos (hb i)), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hε j hj)
  obtain ⟨ε, hpos, hε⟩ := hε
  obtain ⟨x, hx⟩ := LubinTate.Valuations.absoluteValueApproximation
    (fun i => (D i).realAbsoluteValue)
    (fun i => (LubinTate.Valuations.not_trivialAbsoluteValue_iff_isNontrivial _).mpr
      (D i).realAbsoluteValue_isNontrivial)
    (fun i j hij h => hD hij ((realAbsoluteValue_isEquiv_iff (D i) (D j)).mp
      ((LubinTate.Valuations.equivalentAbsoluteValues_iff_isEquiv _ _).mp h))) a hpos
  refine ⟨x, fun i => ((D i).realAbsoluteValue_lt_iff _ _).mp ?_⟩
  exact (hx i).trans_le (hε i (Finset.mem_univ i))

end ValuationTheory.DiscreteValuationField.DVF
