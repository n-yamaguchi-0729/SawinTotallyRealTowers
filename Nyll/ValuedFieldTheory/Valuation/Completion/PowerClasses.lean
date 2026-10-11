/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.WeakApproximation
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion
import Nyll.ValuedFieldTheory.Valuation.Henselian.PrincipalUnitRoots
import Mathlib.Topology.Algebra.IsOpenUnits
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Simultaneous prescription of power classes in completions

For an integer nonzero in the original field, every finite tuple of local
multiplicative power classes is represented by a single global unit.
Hensel's lemma supplies the open local power subgroups; weak approximation
then supplies the global representative.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

/-- Simultaneous prescription of nth-power classes in a finite collection of
inequivalent discrete completions, without a roots-of-unity hypothesis. -/
theorem surjective_pi_completion_powerClasses
    (D : ι → DVF K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (n : ℕ) (hn : (n : K) ≠ 0) :
    Function.Surjective (fun (u : Kˣ) (i : ι) =>
      (Units.map (algebraMap K (D i).valuation.Completion).toMonoidHom u :
        (D i).valuation.Completionˣ ⧸
          (powMonoidHom n : (D i).valuation.Completionˣ →*
            (D i).valuation.Completionˣ).range)) := by
  classical
  intro c
  cases isEmpty_or_nonempty ι with
  | inl h =>
    let := h
    exact ⟨1, funext (fun i => isEmptyElim i)⟩
  | inr h =>
    let := h
    let N (i : ι) : Subgroup (D i).valuation.Completionˣ :=
      (powMonoidHom n : (D i).valuation.Completionˣ →*
        (D i).valuation.Completionˣ).range
    obtain ⟨a, ha⟩ := Classical.axiomOfChoice
      (fun i => QuotientGroup.mk'_surjective (N i) (c i))
    let U (i : ι) : Set (D i).valuation.Completionˣ :=
      {u | (a i)⁻¹ * u ∈ N i}
    have hN (i : ι) : IsOpen (N i : Set (D i).valuation.Completionˣ) := by
      have : Valuation.IsCompleteDiscrete
          (Valued.v : _root_.Valuation (D i).valuation.Completion (D i).ValueGroup) :=
        Valuation.completion_isCompleteDiscrete (D i).valuation
      have := Valuation.henselianRing
        (Valued.v : _root_.Valuation (D i).valuation.Completion (D i).ValueGroup)
      apply isOpen_unit_pow_range (Γ := (D i).ValueGroup) n
      rw [← map_natCast (algebraMap K (D i).valuation.Completion) n]
      exact (algebraMap K (D i).valuation.Completion).injective.ne hn
    have hU (i : ι) : IsOpen (U i) :=
      (hN i).preimage (continuous_const.mul continuous_id)
    let V (i : ι) : Set (D i).valuation.Completion :=
      Units.val '' U i
    have hV (i : ι) : IsOpen (V i) :=
      IsOpenUnits.isOpenEmbedding_unitsVal.isOpenMap (U i) (hU i)
    have haU (i : ι) : a i ∈ U i := by
      change (a i)⁻¹ * a i ∈ N i
      rw [inv_mul_cancel]
      exact (N i).one_mem
    have hprodOpen : IsOpen (Set.univ.pi V) :=
      isOpen_set_pi Set.finite_univ (fun i _ => hV i)
    have hprodNonempty : (Set.univ.pi V).Nonempty :=
      ⟨fun i => (a i : (D i).valuation.Completion),
        fun i _ => ⟨a i, haU i, rfl⟩⟩
    obtain ⟨x, hx⟩ := (denseRange_pi_completion D hD).exists_mem_open
      hprodOpen hprodNonempty
    have hx0 : x ≠ 0 := by
      obtain ⟨b, _, hb⟩ := hx (Classical.arbitrary ι) (Set.mem_univ _)
      change (b : (D (Classical.arbitrary ι)).valuation.Completion) =
        algebraMap K (D (Classical.arbitrary ι)).valuation.Completion x at hb
      intro hxzero
      rw [hxzero, map_zero] at hb
      exact b.ne_zero hb
    refine ⟨Units.mk0 x hx0, funext (fun i => ?_)⟩
    obtain ⟨b, hbU, hb⟩ := hx i (Set.mem_univ i)
    have hunit : Units.map (algebraMap K (D i).valuation.Completion).toMonoidHom
        (Units.mk0 x hx0) = b := Units.ext hb.symm
    change (Units.map (algebraMap K (D i).valuation.Completion).toMonoidHom
      (Units.mk0 x hx0) : (D i).valuation.Completionˣ ⧸ N i) = c i
    rw [hunit]
    exact (QuotientGroup.eq.mpr hbU).symm.trans (ha i)

end ValuationTheory.DiscreteValuationField.DVF
