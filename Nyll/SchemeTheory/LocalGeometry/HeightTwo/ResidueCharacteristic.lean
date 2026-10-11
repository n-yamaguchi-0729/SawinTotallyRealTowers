/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Residue characteristic at a prime localization

An integer which is a nonunit in a prime localization vanishes in its
residue field.  For a prime integer this determines the residue
characteristic.  We also record the canonical map from a localized branch
quotient to that residue field.
-/

noncomputable section

open IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- A branch contained in the localization prime maps into the maximal ideal
of the prime localization. -/
theorem map_le_maximalIdeal_localizationAtPrime
    {A : Type u} [CommRing A]
    (q P : Ideal A) [P.IsPrime] (hqP : q ≤ P) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) q ≤
      maximalIdeal (Localization.AtPrime P) := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact Ideal.map_mono hqP

/-- The canonical residue map from a branch quotient after localization. -/
noncomputable def localizationAtPrimeBranchQuotientToResidue
    {A : Type u} [CommRing A]
    (q P : Ideal A) [P.IsPrime] (hqP : q ≤ P) :
    (Localization.AtPrime P ⧸
        Ideal.map (algebraMap A (Localization.AtPrime P)) q) →+*
      (Localization.AtPrime P ⧸
        maximalIdeal (Localization.AtPrime P)) :=
  Ideal.Quotient.factor
    (map_le_maximalIdeal_localizationAtPrime q P hqP)

/-- A prime integer which is a nonunit in a prime localization is the
characteristic of its residue field. -/
theorem charP_localizationAtPrime_residue_of_natCast_nonunit
    {A : Type u} [CommRing A]
    (P : Ideal A) [P.IsPrime]
    (p : ℕ) (hp : p.Prime)
    (hp_nonunit :
      ¬ IsUnit
        (algebraMap A (Localization.AtPrime P) (p : A))) :
    CharP
      (Localization.AtPrime P ⧸
        maximalIdeal (Localization.AtPrime P)) p := by
  have hp_nonunit' : ¬ IsUnit (p : Localization.AtPrime P) := by
    simpa only [map_natCast] using hp_nonunit
  rw [CharP.charP_iff_prime_eq_zero hp,
    ← map_natCast (Ideal.Quotient.mk
      (maximalIdeal (Localization.AtPrime P))),
    Ideal.Quotient.eq_zero_iff_mem]
  exact (mem_maximalIdeal _).2 (mem_nonunits_iff.2 hp_nonunit')

end EtaleFundamentalGroups

end
