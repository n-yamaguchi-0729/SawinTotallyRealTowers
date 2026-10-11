/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.Algebra.CharP.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Ring.Int.Units
import Lean.Elab.Tactic.Omega

/-!
# Affine integral models of finitely generated fields
-/

namespace FieldTheory

universe u

/-- A finitely generated field is the fraction field of a finitely generated
algebra over the integers. -/
theorem exists_finiteType_int_model
    (K : Type u) [Field K] (hfg : Field.FG K) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A ∧ IsFractionRing A K := by
  obtain ⟨s, hs⟩ := hfg.finitely_generated
  let A := Algebra.adjoin ℤ (s : Set K)
  refine ⟨A, (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset s), ?_⟩
  apply IsFractionRing.of_field A K
  intro z
  have hz : z ∈ Subfield.closure (s : Set K) := by rw [hs]; exact Subfield.mem_top z
  obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hz
  have haA : a ∈ A := by rw [show A = _ from Algebra.adjoin_int (s : Set K)]; exact ha
  have hbA : b ∈ A := by rw [show A = _ from Algebra.adjoin_int (s : Set K)]; exact hb
  exact ⟨⟨a, haA⟩, ⟨b, hbA⟩, hab.symm⟩

/-- The integers form a Jacobson ring. -/
theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  apply isJacobsonRing_iff_prime_eq.mpr
  intro P hP
  by_cases hzero : P = ⊥
  · subst P
    apply le_antisymm ?_ Ideal.le_jacobson
    intro x hx
    have hu : IsUnit (x * 3 + 1) := (Ideal.mem_jacobson_bot.mp hx) 3
    rcases Int.isUnit_eq_one_or hu with h | h <;>
      simp only [Ideal.mem_bot] <;> omega
  · have : P.IsMaximal := hP.isMaximal hzero
    exact Ideal.jacobson_eq_self_of_isMaximal

/-- A field that is finitely generated as a ring has positive characteristic. -/
theorem ringChar_ne_zero_of_finiteType_int
    (K : Type u) [Field K] [hfin : Algebra.FiniteType ℤ K] : ringChar K ≠ 0 := by
  intro hchar
  have : CharP K 0 := hchar ▸ (inferInstance : CharP K (ringChar K))
  have : CharZero K := CharP.charP_to_charZero K
  have : IsJacobsonRing ℤ := int_isJacobsonRing
  have : Module.Finite ℤ K := finite_of_finite_type_of_isJacobsonRing ℤ K
  have : Algebra.IsIntegral ℤ K := Algebra.IsIntegral.of_finite ℤ K
  exact Int.not_isField
    (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ K)
      (Field.toIsField K))

end FieldTheory
