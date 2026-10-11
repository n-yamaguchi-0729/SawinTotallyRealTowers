/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# The Dedekind ramification-index criterion for unramifiedness

This file records the local commutative-algebra bridge used in the SGA 1 form
of Abhyankar's lemma.  For a nonzero prime of a Dedekind domain, unramifiedness
is exactly separability of the residue-field extension together with
ramification index one.

No completeness or Henselian hypothesis is involved.
-/

namespace TameAbhyankar.SGA1

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- At a nonzero prime of a Dedekind domain, `Algebra.IsUnramifiedAt` is
equivalent to separability of the residue-field extension and ramification
index one. -/
theorem isUnramifiedAt_iff_residue_isSeparable_and_ramificationIdx_eq_one
    [IsDedekindDomain S] [Algebra.EssFiniteType R S]
    {P : Ideal S} [P.IsPrime] (hP : P ≠ ⊥) :
    let : Algebra (Localization.AtPrime (P.under R))
        (Localization.AtPrime P) :=
      Localization.AtPrime.algebraOfLiesOver (P.under R) P
    Algebra.IsUnramifiedAt R P ↔
      Algebra.IsSeparable (P.under R).ResidueField P.ResidueField ∧
        Ideal.ramificationIdx' (P.under R) P = 1 := by
  let _ : Algebra (Localization.AtPrime (P.under R))
      (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver (P.under R) P
  have hram := Ideal.IsDedekindDomain.ramificationIdx'_eq_one_iff
    (R := R) (S := S) (p := P.under R) (P := P) hP Ideal.map_comap_le
  rw [Algebra.isUnramifiedAt_iff_map_eq R (P.under R) P, hram]

end TameAbhyankar.SGA1
