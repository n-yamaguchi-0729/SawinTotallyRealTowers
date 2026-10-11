/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Residue.Tame
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.UnramifiedCriterion

/-!
# Trivial inertia implies unramifiedness

For a finite Galois extension of Dedekind domains, cardinality one of the
ideal inertia group forces both ramification index one and separability of
the residue extension.  Thus it gives mathlib's `Algebra.IsUnramifiedAt`
without a separate residue-separability hypothesis.
-/

noncomputable section


namespace TameAbhyankar.SGA1

attribute [local instance] Ideal.Quotient.field

variable {A B G : Type*}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B]
variable [Module.Finite A B] [Module.IsTorsionFree A B]
variable [Group G] [Finite G] [MulSemiringAction G B]
variable [IsGaloisGroup G A B]

/-- In a finite Galois Dedekind extension, trivial ideal inertia is
equivalent to the two local conditions needed for unramifiedness, and hence
implies `Algebra.IsUnramifiedAt`. -/
theorem isUnramifiedAt_of_inertia_card_eq_one
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hcard : Nat.card (P.toAddSubgroup.inertia G) = 1) :
    Algebra.IsUnramifiedAt A P := by
  have hformula :=
    inertia_card_eq_ramificationIdx_mul_finInsepDegree
      (A := A) (B := B) (G := G) p hp P
  rw [hcard] at hformula
  have hram : Ideal.ramificationIdx' p P = 1 :=
    Nat.dvd_one.mp ⟨Field.finInsepDegree (A ⧸ p) (B ⧸ P), hformula⟩
  have hcop : Nat.Coprime (Nat.card (P.toAddSubgroup.inertia G))
      (ringExpChar (A ⧸ p)) := by
    rw [hcard]
    simp
  let : Algebra.IsSeparable (A ⧸ p) (B ⧸ P) :=
    residue_isSeparable_of_inertia_card_coprime_ringExpChar
      (A := A) (B := B) (G := G) p hp P hcop
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime P) :=
    Localization.AtPrime.algebraOfLiesOver p P
  let : Algebra.IsSeparable p.ResidueField P.ResidueField :=
    inferInstance
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hconditions :
      Algebra.IsSeparable p.ResidueField P.ResidueField ∧
        Ideal.ramificationIdx' p P = 1 :=
    ⟨inferInstance, hram⟩
  have hover : p = P.under A := P.over_def p
  subst p
  exact
    (isUnramifiedAt_iff_residue_isSeparable_and_ramificationIdx_eq_one
      (R := A) (S := B) (P := P) hP).2 hconditions

end TameAbhyankar.SGA1
