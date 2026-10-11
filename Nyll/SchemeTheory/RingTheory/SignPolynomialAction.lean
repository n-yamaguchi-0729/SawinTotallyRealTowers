/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Int.Units

/-! # Simultaneous sign change on the polynomial ring

The sign group is the concrete group `ℤˣ = {1, -1}`.  Its action is kept as
explicit data, so no competing action on the polynomial ring is registered.
This is the action occurring in Stacks Project, Tag 0BTE.
-/

noncomputable section

namespace SchemeTheory.SignPolynomial

open MvPolynomial

variable (k : Type*) [CommRing k] (n : ℕ)

/-- Simultaneous negation of all polynomial variables as an algebra homomorphism. -/
def simultaneousNegHom : MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (fun i : Fin n => -(X i : MvPolynomial (Fin n) k))

theorem simultaneousNegHom_comp_self :
    (simultaneousNegHom k n).comp (simultaneousNegHom k n) =
      AlgHom.id k (MvPolynomial (Fin n) k) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, simultaneousNegHom, MvPolynomial.aeval_X,
    map_neg, neg_neg, AlgHom.id_apply]

/-- The actual algebra involution sending every `X i` to `-X i`. -/
def simultaneousNeg : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
  AlgEquiv.ofAlgHom (simultaneousNegHom k n) (simultaneousNegHom k n)
    (simultaneousNegHom_comp_self k n) (simultaneousNegHom_comp_self k n)

theorem simultaneousNeg_apply (p : MvPolynomial (Fin n) k) :
    simultaneousNeg k n p = simultaneousNegHom k n p := rfl

@[simp]
theorem simultaneousNeg_X (i : Fin n) :
    simultaneousNeg k n (X i) = -X i := by
  rw [simultaneousNeg_apply, simultaneousNegHom, MvPolynomial.aeval_X]

theorem simultaneousNeg_involutive : Function.Involutive (simultaneousNeg k n) := by
  intro p
  exact AlgHom.congr_fun (simultaneousNegHom_comp_self k n) p

theorem simultaneousNeg_mul_self : simultaneousNeg k n * simultaneousNeg k n = 1 := by
  apply AlgEquiv.ext
  intro p
  exact simultaneousNeg_involutive k n p

/-- The action homomorphism of the two-element group of integer units. -/
def signActionHom : ℤˣ →* (MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k) where
  toFun ε := if ε = 1 then 1 else simultaneousNeg k n
  map_one' := ite_eq_left rfl
  map_mul' ε δ := by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp only [one_mul, ite_true]
    · rcases Int.units_eq_one_or δ with rfl | rfl
      · simp only [mul_one, ite_true]
      · have hneg : (-1 : ℤˣ) ≠ 1 := by decide
        have hmul : (-1 : ℤˣ) * (-1) = 1 := by decide
        simp only [hmul, ite_true, ite_eq_right hneg, simultaneousNeg_mul_self]

theorem signActionHom_apply (ε : ℤˣ) :
    signActionHom k n ε = if ε = 1 then 1 else simultaneousNeg k n := rfl

/-- The sign action on the polynomial algebra, supplied as explicit data. -/
@[instance_reducible]
def signAction : MulSemiringAction ℤˣ (MvPolynomial (Fin n) k) :=
  MulSemiringAction.compHom (MvPolynomial (Fin n) k) (signActionHom k n)

theorem signAction_neg_one (p : MvPolynomial (Fin n) k) :
    (signAction k n).smul (-1 : ℤˣ) p = simultaneousNeg k n p := by
  change (signActionHom k n (-1)) p = simultaneousNeg k n p
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  simp only [signActionHom_apply, ite_eq_right hneg]

/-- Fixed by the entire sign group is equivalent to fixed by simultaneous negation. -/
theorem signAction_fixed_iff (p : MvPolynomial (Fin n) k) :
    (∀ ε : ℤˣ, (signAction k n).smul ε p = p) ↔ simultaneousNeg k n p = p := by
  change (∀ ε : ℤˣ, (signActionHom k n ε) p = p) ↔ simultaneousNeg k n p = p
  have hneg : (-1 : ℤˣ) ≠ 1 := by decide
  constructor
  · intro h
    simpa only [signActionHom_apply, ite_eq_right hneg] using h (-1)
  · intro h ε
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simp only [signActionHom_apply, ite_true, AlgEquiv.one_apply]
    · simpa only [signActionHom_apply, ite_eq_right hneg] using h

/-- The fixed subalgebra of the simultaneous sign action. -/
def fixedSubalgebra : Subalgebra k (MvPolynomial (Fin n) k) :=
  AlgHom.equalizer (simultaneousNegHom k n) (AlgHom.id k (MvPolynomial (Fin n) k))

theorem mem_fixedSubalgebra_iff (p : MvPolynomial (Fin n) k) :
    p ∈ fixedSubalgebra k n ↔ simultaneousNeg k n p = p := Iff.rfl

theorem mem_fixedSubalgebra_iff_forall_signAction (p : MvPolynomial (Fin n) k) :
    p ∈ fixedSubalgebra k n ↔ ∀ ε : ℤˣ, (signAction k n).smul ε p = p := by
  exact (mem_fixedSubalgebra_iff k n p).trans (signAction_fixed_iff k n p).symm

end SchemeTheory.SignPolynomial
