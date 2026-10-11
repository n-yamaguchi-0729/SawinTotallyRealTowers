/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteNormValuation
import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
import Nyll.ValuedFieldTheory.Valuation.DiscreteEquivalence
import Nyll.ValuedFieldTheory.Valuation.ValuedAdicComplete
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.RingTheory.AdicCompletion.Topology

/-!
# Complete valuations on arbitrary finite extensions

The field norm constructs a discrete extension with the original value group.
The complete absolute-value extension supplies adic completeness through its
actual norm formula. Separability and residue-field perfection are not required.
-/

noncomputable section
namespace ValuationTheory.DiscreteValuationField.ValuedExtension
open AlgebraicNumberTheory.Valuations
open scoped NNReal
universe u v w
/-- Adic completeness of a discrete valuation ring implies completeness for
its actual valuation uniformity, with an arbitrary ambient value group. -/
theorem completeSpace_of_completeDiscreteValuation
    {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]
    (v : _root_.Valuation F Γ) [Valuation.IsCompleteDiscrete v] :
    @CompleteSpace F (Valued.mk' v).toUniformSpace := by
  let : Valued F Γ := Valued.mk' v
  let : v.RankOne := _root_.Valuation.IsRankOneDiscrete.rankOne v (e := 2) (by norm_num)
  let : NormedField F := Valued.toNormedField F Γ
  let w : _root_.Valuation F ℝ≥0 := NormedField.valuation
  have hring : v.valuationSubring = w.valuationSubring := by
    ext x
    change v x ≤ 1 ↔ ‖x‖₊ ≤ 1
    rw [← NNReal.coe_le_one]
    exact (Valued.toNormedField.norm_le_one_iff).symm
  have : w.IsRankOneDiscrete :=
    ((_root_.Valuation.isEquiv_iff_valuationSubring _ _).mpr hring).isRankOneDiscrete
  have hadicComplete : IsAdicComplete (IsLocalRing.maximalIdeal w.valuationSubring)
      w.valuationSubring := by
    let P : ValuationSubring F → Prop := fun O => IsAdicComplete (IsLocalRing.maximalIdeal O) O
    exact hring ▸ (show P v.valuationSubring from Valuation.isAdicComplete v)
  let : Valued F ℝ≥0 := NormedField.toValued
  have hadic : IsAdic (IsLocalRing.maximalIdeal w.valuationSubring) :=
    Valuations.rankOneDiscreteValuationSubring_isAdic (K := F) (Gamma := ℝ≥0)
  have hcomplete : CompleteSpace w.valuationSubring :=
    (hadic.isAdicComplete_iff.mp hadicComplete).1
  have hset : IsComplete (w.valuationSubring : Set F) := by
    have h := (completeSpace_iff_isComplete_univ (α := w.valuationSubring)).mp hcomplete
    rw [Subtype.isComplete_iff, Set.image_univ, Subtype.range_coe_subtype] at h
    exact h
  apply NormedField.completeSpace_iff_isComplete_closedBall.mpr
  have heq : (w.valuationSubring : Set F) = Metric.closedBall (0 : F) 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
    rw [dist_zero_right, ← NNReal.coe_le_one]
    rfl
  exact heq ▸ hset

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable {Γ : Type v} [LinearOrderedCommGroupWithZero Γ] [Valued K Γ]
variable [(Valued.v : _root_.Valuation K Γ).RankOne] [CompleteSpace K]

/-- The norm valuation takes values in the cyclic value group of the base. -/
theorem finiteNormValuation_isRankOneDiscrete_general
    [(Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete] :
    (finiteNormValuation (K := K) (L := L) (Γ := Γ)).IsRankOneDiscrete := by
  let vL : _root_.Valuation L Γ := finiteNormValuation (K := K) (L := L)
  have hle : vL.valueGroup ≤ (Valued.v : _root_.Valuation K Γ).valueGroup := by
    apply (Subgroup.closure_le _).2
    intro γ hγ
    obtain ⟨x, hx⟩ := hγ
    exact MonoidWithZeroHom.mem_valueGroup _ ⟨Algebra.norm K x, hx⟩
  have : IsCyclic vL.valueGroup := Subgroup.isCyclic_of_le hle
  have : vL.IsNontrivial := finiteNormValuation_isNontrivial
  exact _root_.Valuation.IsRankOneDiscrete.mk' vL

private theorem normAbsoluteValue_complete
    (F : Type*) [NormedField F] [CompleteSpace F] :
    IsCompleteForAbsoluteValue (NormedField.toAbsoluteValue F) := by
  apply (absoluteValueCompleteness_completeSpace_withAbs_iff_complete _).1
  let e : WithAbs (NormedField.toAbsoluteValue F) ≃ᵢ F :=
    { toEquiv := (WithAbs.equiv (NormedField.toAbsoluteValue F)).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub, WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub]
        rfl }
  exact e.completeSpace

/-- Finite extensions carry a complete norm valuation, including inseparable extensions. -/
theorem finiteNormValuation_isCompleteDiscrete
    [(Valued.v : _root_.Valuation K Γ).IsRankOneDiscrete] :
    Valuation.IsCompleteDiscrete
      (finiteNormValuation (K := K) (L := L) (Γ := Γ)) := by
  let : NontriviallyNormedField K := Valued.toNontriviallyNormedField K Γ
  let a : AbsoluteValue K ℝ := NormedField.toAbsoluteValue K
  have ha : a.IsNontrivial := by
    obtain ⟨z, hz⟩ := NormedField.exists_one_lt_norm K
    exact ⟨z, norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans hz)), ne_of_gt hz⟩
  have hn : LubinTate.Valuations.NonarchimedeanAbsoluteValue a :=
    LubinTate.Valuations.nonarchimedean_of_strong_triangle a
      (Valued.isNonarchimedean_norm K Γ)
  let R := finiteNormExtension_nonarchimedean_finite_extension
    (L := L) a (normAbsoluteValue_complete K) hn ha
  let : NormedField L := AbsoluteValue.toNormedField R.extension
  have : CompleteSpace L := by
    change @CompleteSpace L (AbsoluteValue.toNormedField R.extension).toUniformSpace
    rw [← absoluteValue_uniformSpace_eq_toNormedField]
    exact R.complete_extension
  have : IsUltrametricDist L :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
      (finiteNormExtension_finite_normFormulaValue_strong_triangle
        a (normAbsoluteValue_complete K) hn ha)
  let val : _root_.Valuation L Γ := finiteNormValuation (K := K) (L := L)
  have : val.IsRankOneDiscrete := finiteNormValuation_isRankOneDiscrete_general
  have heq : val.valuationSubring =
      (NormedField.valuation (K := L)).valuationSubring := by
    ext x
    change val x ≤ 1 ↔ ‖x‖₊ ≤ 1
    rw [← NNReal.coe_le_one]
    change Valued.v (Algebra.norm K x) ≤ 1 ↔ R.extension x ≤ 1
    rw [R.norm_formula]
    change Valued.v (Algebra.norm K x) ≤ 1 ↔
      ‖Algebra.norm K x‖ ^ (1 / (Module.finrank K L : ℝ)) ≤ 1
    have hd : 0 < 1 / (Module.finrank K L : ℝ) := one_div_pos.mpr
      (by exact_mod_cast Module.finrank_pos (R := K) (M := L))
    have hr := Real.rpow_le_rpow_iff (norm_nonneg (Algebra.norm K x)) zero_le_one hd
    rw [Real.one_rpow] at hr
    exact (Valued.toNormedField.norm_le_one_iff).symm.trans hr.symm
  have hw : (NormedField.valuation (K := L)).IsRankOneDiscrete :=
    ((_root_.Valuation.isEquiv_iff_valuationSubring _ _).mpr heq).isRankOneDiscrete
  have hcomplete : IsAdicComplete
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := L)).valuationSubring)
      (NormedField.valuation (K := L)).valuationSubring := by
    let : Valued L ℝ≥0 := NormedField.toValued
    exact Valuations.rankOneDiscreteValuationSubring_isAdicComplete (K := L) (Gamma := ℝ≥0)
  refine { isRankOneDiscrete := inferInstance, isAdicComplete := ?_ }
  let P : ValuationSubring L → Prop := fun O => IsAdicComplete (IsLocalRing.maximalIdeal O) O
  exact heq.symm ▸ (show P (NormedField.valuation (K := L)).valuationSubring from hcomplete)
end ValuationTheory.DiscreteValuationField.ValuedExtension

namespace ValuationTheory.DiscreteValuationField.CompleteDVF
universe u v w
variable {K : Type u} [Field K]

/-- The complete norm valuation on an arbitrary finite field extension. -/
def finiteExtension (base : CompleteDVF.{u, v} K)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] :
    CompleteDVF.{w, v} L := by
  let : Valued K base.ValueGroup := Valued.mk' base.valuation
  let : base.valuation.RankOne :=
    _root_.Valuation.IsRankOneDiscrete.rankOne base.valuation (e := 2) (by norm_num)
  have : CompleteSpace K :=
    ValuedExtension.completeSpace_of_completeDiscreteValuation base.valuation
  have : (Valued.v : _root_.Valuation K base.ValueGroup).IsRankOneDiscrete :=
    inferInstanceAs base.valuation.IsRankOneDiscrete
  exact { ValueGroup := base.ValueGroup
          valuation := ValuedExtension.finiteNormValuation (K := K) (L := L)
          instCompleteDiscrete := ValuedExtension.finiteNormValuation_isCompleteDiscrete }

/-- The constructed complete valuation extends the original one. -/
theorem finiteExtension_hasExtension (base : CompleteDVF.{u, v} K)
    (L : Type w) [Field L] [Algebra K L] [FiniteDimensional K L] :
    base.valuation.HasExtension (base.finiteExtension L).valuation := by
  let : Valued K base.ValueGroup := Valued.mk' base.valuation
  let : base.valuation.RankOne :=
    _root_.Valuation.IsRankOneDiscrete.rankOne base.valuation (e := 2) (by norm_num)
  have : CompleteSpace K :=
    ValuedExtension.completeSpace_of_completeDiscreteValuation base.valuation
  exact ValuedExtension.finiteNormValuation_hasExtension
end ValuationTheory.DiscreteValuationField.CompleteDVF
