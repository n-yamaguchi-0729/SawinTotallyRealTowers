/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.WeakApproximation
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion
import Nyll.ValuedFieldTheory.Valuation.Henselian.ArtinSchreier
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Simultaneous Artin–Schreier classes in valued completions

In characteristic p, the local Artin–Schreier images are open. The diagonal
density from weak approximation therefore realizes any finite collection
of local additive Artin–Schreier classes by a global field element.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]

local instance completion_charP (D : DVF K) (p : ℕ) [CharP K p] :
    CharP D.valuation.Completion p :=
  charP_of_injective_algebraMap (algebraMap K D.valuation.Completion).injective p

/-- Weak approximation for additive Artin–Schreier classes in finitely many
inequivalent discrete completions of a characteristic-p field. -/
theorem surjective_pi_completion_artinSchreierClasses
    (D : ι → DVF K)
    (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    Function.Surjective (fun (x : K) (i : ι) =>
      (algebraMap K (D i).valuation.Completion x :
        (D i).valuation.Completion ⧸
          ((frobenius (D i).valuation.Completion p).toAddMonoidHom -
            AddMonoidHom.id (D i).valuation.Completion).range)) := by
  classical
  intro c
  let N (i : ι) : AddSubgroup (D i).valuation.Completion :=
    ((frobenius (D i).valuation.Completion p).toAddMonoidHom -
      AddMonoidHom.id (D i).valuation.Completion).range
  obtain ⟨a, ha⟩ := Classical.axiomOfChoice
    (fun i => QuotientAddGroup.mk'_surjective (N i) (c i))
  let U (i : ι) : Set (D i).valuation.Completion :=
    {x | -(a i) + x ∈ N i}
  have hN (i : ι) : IsOpen (N i : Set (D i).valuation.Completion) := by
    have : Valuation.IsCompleteDiscrete
        (Valued.v : _root_.Valuation (D i).valuation.Completion (D i).ValueGroup) :=
      Valuation.completion_isCompleteDiscrete (D i).valuation
    have := Valuation.henselianRing
      (Valued.v : _root_.Valuation (D i).valuation.Completion (D i).ValueGroup)
    exact isOpen_artinSchreier_range (Γ := (D i).ValueGroup) p
  have hU (i : ι) : IsOpen (U i) :=
    (hN i).preimage (continuous_const.add continuous_id)
  have haU (i : ι) : a i ∈ U i := by
    change -(a i) + a i ∈ N i
    rw [neg_add_cancel]
    exact (N i).zero_mem
  have hprodOpen : IsOpen (Set.univ.pi U) :=
    isOpen_set_pi Set.finite_univ (fun i _ => hU i)
  have hprodNonempty : (Set.univ.pi U).Nonempty :=
    ⟨a, fun i _ => haU i⟩
  obtain ⟨x, hx⟩ := (denseRange_pi_completion D hD).exists_mem_open
    hprodOpen hprodNonempty
  refine ⟨x, funext (fun i => ?_)⟩
  exact (QuotientAddGroup.eq.mpr (hx i (Set.mem_univ i))).symm.trans (ha i)

end ValuationTheory.DiscreteValuationField.DVF
