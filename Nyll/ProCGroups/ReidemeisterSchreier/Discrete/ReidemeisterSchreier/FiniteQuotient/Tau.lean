/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Data

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Tau

This module defines the finite-state tau rewriting of signed words into
Schreier symbols and proves compatibility with concatenation, cancellation,
reduction, and free-group multiplication.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)

/-- Schreier rewriting of a raw word list, indexed by quotient states. -/
def tauList : Q → List (X × Bool) → FreeGroup (FiniteSchreierSymbol X Q)
  | _q, [] => 1
  | q, (x, true) :: xs =>
      FreeGroup.of (q, x) * tauList (D.transition q x) xs
  | q, (x, false) :: xs =>
      (FreeGroup.of (D.inverseTransition q x, x))⁻¹ *
        tauList (D.inverseTransition q x) xs

/-- The \(\tau\)-list rewrite is unchanged when adjacent inverse letters cancel. -/
@[simp]
theorem tauList_cons_true_false
    (q : Q) (x : X) (xs : List (X × Bool)) :
    D.tauList q ((x, true) :: (x, false) :: xs) =
      D.tauList q xs := by
  simp only [tauList, transition_eq, inverseTransition_eq, mul_inv_cancel_right,
      mul_inv_cancel_left]

/-- The \(\tau\)-list rewrite is unchanged when adjacent inverse letters cancel. -/
@[simp]
theorem tauList_cons_false_true
    (q : Q) (x : X) (xs : List (X × Bool)) :
    D.tauList q ((x, false) :: (x, true) :: xs) =
      D.tauList q xs := by
  simp only [tauList, inverseTransition_eq, transition_eq, inv_mul_cancel_right,
      inv_mul_cancel_left]

/-- The \(\tau\)-list rewrite is unchanged when adjacent inverse letters cancel. -/
@[simp]
theorem tauList_cons_cancel
    (q : Q) (x : X) (b : Bool) (xs : List (X × Bool)) :
    D.tauList q ((x, b) :: (x, !b) :: xs) =
      D.tauList q xs := by
  cases b
  · exact D.tauList_cons_false_true q x xs
  · exact D.tauList_cons_true_false q x xs

/--
The \(\tau\)-list rewrite of a concatenated word splits as the product of the first rewrite and
the rewrite of the second word from the updated quotient element.
-/
theorem tauList_append
    (q : Q) (xs ys : List (X × Bool)) :
    D.tauList q (xs ++ ys) =
      D.tauList q xs *
        D.tauList
          (D.quotientMap (D.quotientSection q * FreeGroup.mk xs)) ys := by
  induction xs generalizing q with
  | nil =>
      rw [← FreeGroup.one_eq_mk]
      simp only [List.nil_append, tauList, mul_one, quotientMap_quotientSection_apply, one_mul]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · simp only [List.cons_append, tauList, inverseTransition_eq, ih, map_mul,
          quotientMap_quotientSection_apply,
  mul_assoc, SchreierRewriting.mk_cons_false, map_inv]
      · simp only [List.cons_append, tauList, transition_eq, ih, map_mul,
          quotientMap_quotientSection_apply,
  mul_assoc, SchreierRewriting.mk_cons_true]

/-- A single free-group reduction step does not change the \(\tau\)-list rewrite. -/
theorem tauList_redStep
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red.Step xs ys) :
    D.tauList q xs = D.tauList q ys := by
  cases h with
  | not =>
      rw [tauList_append, tauList_append]
      simp only [map_mul, quotientMap_quotientSection_apply, tauList_cons_cancel]

/-- Free-group reduction does not change the \(\tau\)-list rewrite. -/
theorem tauList_red
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.Red xs ys) :
    D.tauList q xs = D.tauList q ys := by
  induction h with
  | refl =>
      rfl
  | tail _ hstep ih =>
      exact ih.trans (D.tauList_redStep q hstep)

/-- The \(\tau\)-lists agree when the corresponding quotient generators agree. -/
theorem tauList_eq_of_mk_eq
    (q : Q) {xs ys : List (X × Bool)}
    (h : FreeGroup.mk xs = FreeGroup.mk ys) :
    D.tauList q xs = D.tauList q ys := by
  rcases FreeGroup.Red.exact.1 h with ⟨zs, hxs, hys⟩
  exact (D.tauList_red q hxs).trans (D.tauList_red q hys).symm

/-- Evaluating a \(\tau\)-list gives the quotient-section conjugate of the represented word. -/
@[simp 900]
theorem symbolEvalHom_tauList
    (q : Q) (xs : List (X × Bool)) :
    D.symbolEvalHom (D.tauList q xs) =
      D.quotientSection q * FreeGroup.mk xs *
        (D.quotientSection
          (D.quotientMap (D.quotientSection q * FreeGroup.mk xs)))⁻¹ := by
  induction xs generalizing q with
  | nil =>
      rw [← FreeGroup.one_eq_mk]
      simp only [tauList, map_one, mul_one, quotientMap_quotientSection_apply, mul_inv_cancel]
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · simp only [tauList, inverseTransition_eq, map_mul, map_inv, symbolEvalHom_of,
          symbolEval_apply, transition,
  quotientMap_quotientSection_apply, mul_assoc, inv_mul_cancel, mul_one, mul_inv_rev, inv_inv, ih,
  inv_mul_cancel_left, SchreierRewriting.mk_cons_false]
      · simp only [tauList, transition_eq, map_mul, symbolEvalHom_of, symbolEval_apply,
          mul_assoc, ih,
  quotientMap_quotientSection_apply, inv_mul_cancel_left, SchreierRewriting.mk_cons_true]

variable [DecidableEq X]

/-- Finite-quotient Schreier rewriting of a free-group word. -/
def tau (q : Q) (w : FreeGroup X) : FreeGroup (FiniteSchreierSymbol X Q) :=
  D.tauList q w.toWord

/-- The \(\tau\)-word for the identity case evaluates to the identity. -/
@[simp]
theorem tau_one (q : Q) :
    D.tau q 1 = 1 := by
  simp only [tau, FreeGroup.toWord_one, tauList]

/-- \(\tau\)-rewriting of a single generator gives the corresponding finite Schreier symbol. -/
@[simp]
theorem tau_of (q : Q) (x : X) :
    D.tau q (FreeGroup.of x) = FreeGroup.of (q, x) := by
  simp only [tau, FreeGroup.toWord_of, tauList, mul_one]

/-- The \(\tau\)-rewrite of \(\mathrm{FreeGroup.mk}(xs)\) agrees with rewriting the list \(xs\). -/
theorem tau_mk (q : Q) (xs : List (X × Bool)) :
    D.tau q (FreeGroup.mk xs) = D.tauList q xs := by
  rw [tau, FreeGroup.toWord_mk]
  exact (D.tauList_red q FreeGroup.reduce.red).symm

/-- Evaluating a \(\tau\)-word gives the quotient-section conjugate of the rewritten word. -/
theorem symbolEvalHom_tau (q : Q) (w : FreeGroup X) :
    D.symbolEvalHom (D.tau q w) =
      D.quotientSection q * w *
        (D.quotientSection (D.quotientMap (D.quotientSection q * w)))⁻¹ := by
  simp only [tau, symbolEvalHom_tauList, FreeGroup.mk_toWord, map_mul,
      quotientMap_quotientSection_apply]

/--
The \(\tau\)-rewrite of a product factors into the rewrite of the first word and the rewrite of
the second word from the updated quotient element.
-/
theorem tau_mul (q : Q) (u v : FreeGroup X) :
    D.tau q (u * v) =
      D.tau q u *
        D.tau (D.quotientMap (D.quotientSection q * u)) v := by
  calc
    D.tau q (u * v) =
        D.tau q (FreeGroup.mk (u.toWord ++ v.toWord)) := by
          rw [← FreeGroup.mul_mk, FreeGroup.mk_toWord, FreeGroup.mk_toWord]
    _ = D.tauList q (u.toWord ++ v.toWord) := D.tau_mk q (u.toWord ++ v.toWord)
    _ =
        D.tauList q u.toWord *
          D.tauList (D.quotientMap (D.quotientSection q * FreeGroup.mk u.toWord))
            v.toWord := by
          rw [tauList_append]
    _ =
        D.tau q u *
          D.tau (D.quotientMap (D.quotientSection q * u)) v := by
          simp only [FreeGroup.mk_toWord, map_mul, quotientMap_quotientSection_apply, tau]

/--
For a kernel word, the \(\tau\)-rewriting preserves products from the identity quotient element.
-/
theorem tau_mul_of_mem_kernel
    {u v : FreeGroup X} (hu : u ∈ D.kernel) :
    D.tau 1 (u * v) = D.tau 1 u * D.tau 1 v := by
  have huquot : D.quotientMap u = 1 := by
    simpa [kernel] using hu
  simpa [D.quotientSection_one, huquot] using D.tau_mul 1 u v

/--
The \(\tau\)-rewrite of an inverse is the inverse of the \(\tau\)-rewrite from the updated
quotient element.
-/
theorem tau_inv (q : Q) (u : FreeGroup X) :
    D.tau (D.quotientMap (D.quotientSection q * u)) u⁻¹ =
      (D.tau q u)⁻¹ := by
  have hmul :
      D.tau q u *
          D.tau (D.quotientMap (D.quotientSection q * u)) u⁻¹ = 1 := by
    simpa using (D.tau_mul q u u⁻¹).symm
  calc
    D.tau (D.quotientMap (D.quotientSection q * u)) u⁻¹ =
        1 * D.tau (D.quotientMap (D.quotientSection q * u)) u⁻¹ := by
          simp only [map_mul, quotientMap_quotientSection_apply, one_mul]
    _ =
        ((D.tau q u)⁻¹ * D.tau q u) *
          D.tau (D.quotientMap (D.quotientSection q * u)) u⁻¹ := by
          simp only [map_mul, quotientMap_quotientSection_apply, one_mul, inv_mul_cancel]
    _ =
        (D.tau q u)⁻¹ *
          (D.tau q u *
            D.tau (D.quotientMap (D.quotientSection q * u)) u⁻¹) := by
          group
    _ = (D.tau q u)⁻¹ := by
          rw [hmul]
          simp only [mul_one]

/--
For a kernel word, the \(\tau\)-rewriting commutes with inversion from the identity quotient
element.
-/
theorem tau_inv_of_mem_kernel
    {u : FreeGroup X} (hu : u ∈ D.kernel) :
    D.tau 1 u⁻¹ = (D.tau 1 u)⁻¹ := by
  have huquot : D.quotientMap u = 1 := by
    simpa [kernel] using hu
  simpa [D.quotientSection_one, huquot] using D.tau_inv 1 u

/--
For a kernel word, evaluating its \(\tau\)-rewrite from the identity quotient state recovers the
original word.
-/
theorem symbolEvalHom_tau_of_mem_kernel
    {w : FreeGroup X} (hw : w ∈ D.kernel) :
    D.symbolEvalHom (D.tau 1 w) = w := by
  have hwquot : D.quotientMap w = 1 := by
    simpa [kernel] using hw
  rw [symbolEvalHom_tau]
  simp only [D.quotientSection_one, one_mul, hwquot, inv_one, mul_one]

/--
The finite-quotient Schreier relator set consists of the \(\tau\)-rewrites of the original
relators at all quotient states.
-/
def schreierRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  { q | ∃ s : Q, ∃ r ∈ R, q = D.tau s r }

end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
