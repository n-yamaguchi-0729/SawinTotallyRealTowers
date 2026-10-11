/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.WeakApproximation
import Nyll.ValuedFieldTheory.Valuation.Completion.WithValScalars
import Mathlib.Topology.NhdsWithin

/-!
# Simultaneous density in valued completions

Weak approximation gives a dense diagonal embedding in a finite product of
inequivalent valued fields, and hence in the product of their completions.
-/

namespace ValuationTheory.DiscreteValuationField.DVF

open scoped Topology

variable {K : Type*} [Field K] {ι : Type*} [Finite ι]
  (D : ι → DVF K)
  (hD : Pairwise (fun i j => ¬ (D i).valuation.IsEquiv (D j).valuation))

include hD

/-- The diagonal embedding into finitely many inequivalent valued copies of
the same field has dense range. -/
theorem denseRange_pi_withVal :
    DenseRange (fun x : K => fun i => WithVal.toVal (D i).valuation x) := by
  intro a
  apply mem_closure_iff.mpr
  intro U hU ha
  have hUnhds := hU.mem_nhds ha
  rw [nhds_pi, Filter.mem_pi'] at hUnhds
  obtain ⟨I, V, hV, hVU⟩ := hUnhds
  have hradius (i : ι) : ∃ b : K, b ≠ 0 ∧
      ∀ x : K, (D i).valuation (x - WithVal.equiv (D i).valuation (a i)) <
          (D i).valuation b →
        WithVal.toVal (D i).valuation x ∈ V i := by
    let v : _root_.Valuation (WithVal (D i).valuation) (D i).ValueGroup := Valued.v
    obtain ⟨γ, hγ⟩ := (Valued.mem_nhds (Γ₀ := (D i).ValueGroup)).mp (hV i)
    obtain ⟨b, hb⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass v) (γ : v.ValueGroup₀)
    have hb0 : b ≠ 0 := by
      intro hzero
      subst b
      rw [map_zero] at hb
      exact (Units.ne_zero γ) hb.symm
    refine ⟨WithVal.equiv (D i).valuation b, ?_, ?_⟩
    · exact (map_ne_zero (WithVal.equiv (D i).valuation)).mpr hb0
    · intro x hx
      apply hγ
      change v.restrict
        (WithVal.toVal (D i).valuation x - a i) < (γ : v.ValueGroup₀)
      rw [← hb]
      apply v.restrict_lt_iff.mpr
      exact hx
  choose b hb hball using hradius
  obtain ⟨x, hx⟩ := exists_forall_valuation_sub_lt D hD
    (fun i => WithVal.equiv (D i).valuation (a i)) b hb
  exact ⟨fun i => WithVal.toVal (D i).valuation x,
    hVU (fun i _ => hball i x (hx i)), ⟨x, rfl⟩⟩

/-- The original field is dense diagonally in the finite product of its
completions at pairwise inequivalent discrete valuations. -/
theorem denseRange_pi_completion :
    DenseRange (fun x : K => fun i =>
      algebraMap K (D i).valuation.Completion x) := by
  let f : (i : ι) → WithVal (D i).valuation → (D i).valuation.Completion :=
    fun _ => UniformSpace.Completion.coe'
  have hdense : DenseRange (Pi.map f) :=
    DenseRange.piMap (fun _ => UniformSpace.Completion.denseRange_coe)
  exact hdense.comp (denseRange_pi_withVal D hD)
    (continuous_pi (fun i =>
      (UniformSpace.Completion.continuous_coe
        (α := WithVal (D i).valuation)).comp (continuous_apply i)))

end ValuationTheory.DiscreteValuationField.DVF
