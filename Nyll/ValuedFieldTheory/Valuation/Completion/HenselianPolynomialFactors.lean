/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianDVF
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableFactorCoefficients
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Descending factors from the completion of a Henselian DVF

The coefficients of a monic divisor of a separable polynomial are separable
over the original field. Separable algebraic closedness in the completion
therefore descends the divisor, preserving monicity and divisibility.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

open Polynomial

variable {K : Type*} [Field K]

/-- A monic factor of a separable polynomial over the valuation completion
descends to a monic factor over the original Henselian field. -/
theorem exists_monic_factor_of_dvd_completion (base : HenselianDVF K)
    {f : K[X]} (hf : f.Separable) {g : base.valuation.Completion[X]}
    (hg : g.Monic) (hdiv : g ∣ f.map (algebraMap K base.valuation.Completion)) :
    ∃ g₀ : K[X], g₀.Monic ∧
      g₀.map (algebraMap K base.valuation.Completion) = g ∧ g₀ ∣ f := by
  have hlifts : g ∈ lifts (algebraMap K base.valuation.Completion) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    exact base.exists_completion_eq_of_isSeparable (g.coeff i)
      (Completion.isSeparable_coeff_of_monic_dvd_map hf hg hdiv i)
  obtain ⟨g₀, hmap, _, hmonic⟩ := lifts_and_degree_eq_and_monic hlifts hg
  refine ⟨g₀, hmonic, hmap, ?_⟩
  apply (map_dvd_map' (algebraMap K base.valuation.Completion)).mp
  rwa [hmap]

/-- Every separable irreducible polynomial stays irreducible after completing
a Henselian discretely valued field. The polynomial need not be monic. -/
theorem irreducible_map_completion (base : HenselianDVF K)
    {f : K[X]} (hf : f.Separable) (hirr : Irreducible f) :
    Irreducible (f.map (algebraMap K base.valuation.Completion)) := by
  have hne : f.map (algebraMap K base.valuation.Completion) ≠ 0 :=
    map_ne_zero hirr.ne_zero
  have hunit : ¬ IsUnit (f.map (algebraMap K base.valuation.Completion)) :=
    (isUnit_map (algebraMap K base.valuation.Completion)).not.mpr hirr.not_isUnit
  apply (irreducible_iff_lt_natDegree_lt hne hunit).mpr
  intro g hg hdegree hdiv
  obtain ⟨g₀, hg₀, hmap, hdiv₀⟩ :=
    base.exists_monic_factor_of_dvd_completion hf hg hdiv
  have hdegree₀ : g₀.natDegree ∈ Finset.Ioc 0 (f.natDegree / 2) := by
    rw [← hmap, natDegree_map, natDegree_map] at hdegree
    exact hdegree
  exact (irreducible_iff_lt_natDegree_lt hirr.ne_zero hirr.not_isUnit).mp
    hirr g₀ hg₀ hdegree₀ hdiv₀

end ValuationTheory.DiscreteValuationField.HenselianDVF
