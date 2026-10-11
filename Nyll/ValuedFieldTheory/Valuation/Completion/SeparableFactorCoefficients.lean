/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Splits

/-!
# Separable coefficients of monic factors

The roots of a factor of a separable ground-field polynomial belong to the
relative separable closure. A monic factor therefore has its coefficients
in that closure, even when the ambient field extension is not algebraic.
-/

namespace ValuationTheory.Completion

open Polynomial

/-- Every coefficient of a monic factor of a separable ground-field
polynomial is separable over the ground field. -/
theorem isSeparable_coeff_of_monic_dvd_map
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    {f : K[X]} (hf : f.Separable) {g : L[X]} (hg : g.Monic)
    (hdiv : g ∣ f.map (algebraMap K L)) (i : ℕ) :
    IsSeparable K (g.coeff i) := by
  let Ω := AlgebraicClosure L
  let E : IntermediateField K Ω := separableClosure K Ω
  let q : Ω[X] := g.map (algebraMap L Ω)
  have hdivΩ : q ∣ f.map (algebraMap K Ω) := by
    have h := Polynomial.map_dvd (algebraMap L Ω) hdiv
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq K L Ω] at h
    exact h
  have hfΩ : f.map (algebraMap K Ω) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K Ω).injective).mpr hf.ne_zero
  have hroots : ∀ a ∈ q.roots, a ∈ E.val.toRingHom.range := by
    intro a ha
    have hfa : a ∈ (f.map (algebraMap K Ω)).roots :=
      Multiset.mem_of_le (Polynomial.roots.le_of_dvd hfΩ hdivΩ) ha
    have hzero : aeval a f = 0 :=
      (Polynomial.mem_roots_map_of_injective
        (algebraMap K Ω).injective hf.ne_zero).mp hfa
    have hsep : IsSeparable K a := hf.of_dvd (minpoly.dvd K a hzero)
    exact ⟨⟨a, mem_separableClosure_iff.mpr hsep⟩, rfl⟩
  have hlifts : q ∈ Polynomial.lifts E.val.toRingHom :=
    (IsAlgClosed.splits q).mem_lift_of_roots_mem_range
      (hg.map (algebraMap L Ω)) E.val.toRingHom hroots
  obtain ⟨c, hc⟩ := (Polynomial.lifts_iff_coeff_lifts q).mp hlifts i
  have hcoeff : IsSeparable K (q.coeff i) := by
    rw [← hc]
    exact mem_separableClosure_iff.mp c.2
  let j : L →ₐ[K] Ω := IsScalarTower.toAlgHom K L Ω
  apply (isSeparable_map_iff j j.injective).mp
  change IsSeparable K (algebraMap L Ω (g.coeff i))
  simpa only [q, Polynomial.coeff_map] using hcoeff

end ValuationTheory.Completion
