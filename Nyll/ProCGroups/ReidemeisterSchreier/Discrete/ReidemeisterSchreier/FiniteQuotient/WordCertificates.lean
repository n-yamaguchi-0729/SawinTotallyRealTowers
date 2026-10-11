/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Kernel

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Word Certificates

This module records checkable prefix-closure conditions for quotient-section
words and proves the reduced-word and state-transition facts required by the
finite tau presentation.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

/--
Prefix-closedness along a concrete word list, starting at quotient state \(q\). Positive letters
require the next representative to be obtained by appending \(x\); negative letters require the
current representative to be obtained by appending \(x\) to the previous state.
-/
def prefixClosedAlongList (D : FiniteQuotientSchreierData X Q) :
    Q → List (X × Bool) → Prop
  | _q, [] => True
  | q, (x, true) :: xs =>
      D.quotientSection (D.transition q x) =
        D.quotientSection q * FreeGroup.of x ∧
      prefixClosedAlongList D (D.transition q x) xs
  | q, (x, false) :: xs =>
      D.quotientSection q =
        D.quotientSection (D.inverseTransition q x) * FreeGroup.of x ∧
      prefixClosedAlongList D (D.inverseTransition q x) xs

/--
Word-level prefix-closedness certificate for a chosen representative-word function. This is
easier to produce from a finite search tree than group equalities of representatives.
-/
def prefixClosedQuotientSectionWordAlongList
    (D : FiniteQuotientSchreierData X Q)
    (quotientSectionWord : Q → List (X × Bool)) :
    Q → List (X × Bool) → Prop
  | _q, [] => True
  | q, (x, true) :: xs =>
      quotientSectionWord (D.transition q x) =
        quotientSectionWord q ++ [(x, true)] ∧
      prefixClosedQuotientSectionWordAlongList D quotientSectionWord
        (D.transition q x) xs
  | q, (x, false) :: xs =>
      quotientSectionWord q =
        quotientSectionWord (D.inverseTransition q x) ++ [(x, true)] ∧
      prefixClosedQuotientSectionWordAlongList D quotientSectionWord
        (D.inverseTransition q x) xs

omit [DecidableEq X] in
/-- A prefix-closed quotient-section word along a list gives prefix-closedness along that list. -/
theorem prefixClosedAlongList_of_prefixClosedQuotientSectionWordAlongList
    {quotientSectionWord : Q → List (X × Bool)}
    (hsection :
      ∀ q : Q, D.quotientSection q = FreeGroup.mk (quotientSectionWord q))
    {q : Q} {xs : List (X × Bool)}
    (hprefix :
      D.prefixClosedQuotientSectionWordAlongList quotientSectionWord q xs) :
    D.prefixClosedAlongList q xs := by
  induction xs generalizing q with
  | nil =>
      trivial
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · rcases hprefix with ⟨hstep, htail⟩
        refine ⟨?_, ih htail⟩
        rw [hsection q, hsection (D.inverseTransition q x), hstep]
        change FreeGroup.mk
            (quotientSectionWord (D.inverseTransition q x) ++ [(x, true)]) =
          FreeGroup.mk (quotientSectionWord (D.inverseTransition q x)) *
            FreeGroup.mk [(x, true)]
        rw [FreeGroup.mul_mk]
      · rcases hprefix with ⟨hstep, htail⟩
        refine ⟨?_, ih htail⟩
        rw [hsection (D.transition q x), hsection q, hstep]
        change FreeGroup.mk (quotientSectionWord q ++ [(x, true)]) =
          FreeGroup.mk (quotientSectionWord q) * FreeGroup.mk [(x, true)]
        rw [FreeGroup.mul_mk]

/-- The chosen quotient section is prefix closed on its own representative words. -/
def IsPrefixClosedQuotientSection : Prop :=
  ∀ q : Q, D.prefixClosedAlongList 1 (D.quotientSection q).toWord

/-- A prefix-closed quotient-section word certificate gives a prefix-closed quotient section. -/
theorem isPrefixClosedQuotientSection_of_prefixClosedQuotientSectionWord
    {quotientSectionWord : Q → List (X × Bool)}
    (hsection :
      ∀ q : Q, D.quotientSection q = FreeGroup.mk (quotientSectionWord q))
    (hreduced :
      ∀ q : Q, FreeGroup.reduce (quotientSectionWord q) = quotientSectionWord q)
    (hprefix :
      ∀ q : Q,
        D.prefixClosedQuotientSectionWordAlongList quotientSectionWord 1
          (quotientSectionWord q)) :
    D.IsPrefixClosedQuotientSection := by
  intro q
  have hprefix' :=
    D.prefixClosedAlongList_of_prefixClosedQuotientSectionWordAlongList
      hsection (hprefix q)
  simpa [hsection q, FreeGroup.toWord_mk, hreduced q] using hprefix'

omit [DecidableEq X] in
private theorem prefixClosedQuotientSectionWordAlongList_of_positive_prefixStates_from_acc
    {quotientSectionWord : Q → List (X × Bool)}
    (hsection :
      ∀ q : Q, D.quotientSection q = FreeGroup.mk (quotientSectionWord q))
    (hpositive :
      ∀ q : Q, ∀ xb ∈ quotientSectionWord q, xb.2 = true)
    (hprefixState :
      ∀ q : Q, ∀ acc rest : List (X × Bool),
        acc ++ rest = quotientSectionWord q →
          quotientSectionWord (D.quotientMap (FreeGroup.mk acc)) = acc)
    (target : Q) :
    ∀ acc rest : List (X × Bool),
      acc ++ rest = quotientSectionWord target →
      quotientSectionWord (D.quotientMap (FreeGroup.mk acc)) = acc →
      D.prefixClosedQuotientSectionWordAlongList quotientSectionWord
        (D.quotientMap (FreeGroup.mk acc)) rest
  | _acc, [], _hcat, _hacc => by
      trivial
  | acc, (x, eps) :: xs, hcat, hacc => by
      have heps : eps = true := by
        exact hpositive target (x, eps) (by
          rw [← hcat]
          exact List.mem_append_right acc (by simp only [List.mem_cons, true_or]))
      cases eps
      · cases heps
      · have hnext :
              quotientSectionWord
                  (D.quotientMap (FreeGroup.mk (acc ++ [(x, true)]))) =
                acc ++ [(x, true)] :=
            hprefixState target (acc ++ [(x, true)]) xs (by
              simpa [List.append_assoc] using hcat)
        have htransition :
              D.transition (D.quotientMap (FreeGroup.mk acc)) x =
                D.quotientMap (FreeGroup.mk (acc ++ [(x, true)])) := by
          simp only [transition, hsection, hacc, map_mul]
          rw [← D.quotientMap.map_mul]
          change
            D.quotientMap (FreeGroup.mk acc * FreeGroup.mk [(x, true)]) =
              D.quotientMap (FreeGroup.mk (acc ++ [(x, true)]))
          rw [FreeGroup.mul_mk]
        refine ⟨?_, ?_⟩
        · calc
            quotientSectionWord (D.transition (D.quotientMap (FreeGroup.mk acc)) x) =
                quotientSectionWord
                  (D.quotientMap (FreeGroup.mk (acc ++ [(x, true)]))) := by
                  rw [htransition]
            _ = acc ++ [(x, true)] := hnext
            _ = quotientSectionWord (D.quotientMap (FreeGroup.mk acc)) ++
                [(x, true)] := by rw [hacc]
        · have htail :=
            prefixClosedQuotientSectionWordAlongList_of_positive_prefixStates_from_acc
              hsection hpositive hprefixState target
              (acc ++ [(x, true)]) xs
              (by simpa [List.append_assoc] using hcat)
              (hprefixState target (acc ++ [(x, true)]) xs (by
                simpa [List.append_assoc] using hcat))
          change D.prefixClosedQuotientSectionWordAlongList quotientSectionWord
            (D.transition (D.quotientMap (FreeGroup.mk acc)) x) xs
          rw [htransition]
          exact htail

omit [DecidableEq X] in
/--
Positive prefix states along a word give a prefix-closed quotient-section word along the list.
-/
theorem prefixClosedQuotientSectionWordAlongList_of_positive_prefixStates
    {quotientSectionWord : Q → List (X × Bool)}
    (hsection :
      ∀ q : Q, D.quotientSection q = FreeGroup.mk (quotientSectionWord q))
    (hpositive :
      ∀ q : Q, ∀ xb ∈ quotientSectionWord q, xb.2 = true)
    (hprefixState :
      ∀ q : Q, ∀ acc rest : List (X × Bool),
        acc ++ rest = quotientSectionWord q →
          quotientSectionWord (D.quotientMap (FreeGroup.mk acc)) = acc)
    (q : Q) :
    D.prefixClosedQuotientSectionWordAlongList quotientSectionWord 1
      (quotientSectionWord q) := by
  have hstart :
      quotientSectionWord (D.quotientMap (FreeGroup.mk ([] : List (X × Bool)))) =
        ([] : List (X × Bool)) :=
    hprefixState q [] (quotientSectionWord q) (by simp only [List.nil_append])
  have hprefixClosedFromStart :=
    prefixClosedQuotientSectionWordAlongList_of_positive_prefixStates_from_acc
      D hsection hpositive hprefixState q [] (quotientSectionWord q)
      (by simp only [List.nil_append]) hstart
  have hstate :
      D.quotientMap (FreeGroup.mk ([] : List (X × Bool))) = 1 := by
    rw [← FreeGroup.one_eq_mk, D.quotientMap.map_one]
  simpa [hstate] using hprefixClosedFromStart

omit [DecidableEq X] in
/-- A word list whose letters all have positive sign is reduced. -/
theorem isReduced_of_forall_snd_eq_true :
    ∀ {word : List (X × Bool)},
      (∀ xb ∈ word, xb.2 = true) → FreeGroup.IsReduced word
  | [], _hpositive => by
      simp only [FreeGroup.IsReduced.nil]
  | [_x], _hpositive => by
      simp only [FreeGroup.IsReduced.singleton]
  | x :: y :: xs, hpositive => by
      rw [FreeGroup.isReduced_cons_cons]
      refine ⟨?_, ?_⟩
      · intro _hxy
        rw [hpositive x (by simp only [List.mem_cons, true_or]), hpositive y (by simp only
            [List.mem_cons, true_or, or_true])]
      · exact isReduced_of_forall_snd_eq_true (by
          intro xb hxb
          exact hpositive xb (by simp only [List.mem_cons, hxb, or_true]))

omit D [Group Q] [Fintype Q] in
/-- A word list whose letters all have positive sign is unchanged by free reduction. -/
theorem reduce_eq_of_forall_snd_eq_true
    {word : List (X × Bool)}
    (hpositive : ∀ xb ∈ word, xb.2 = true) :
    FreeGroup.reduce word = word :=
  (isReduced_of_forall_snd_eq_true (X := X) hpositive).reduce_eq

omit [DecidableEq X] in
/--
In a reduced appended prefix-closed quotient-section word, each letter in the added part has
positive sign.
-/
theorem snd_eq_true_of_prefixClosedQuotientSectionWordAlongList_of_isReduced_append
    {quotientSectionWord : Q → List (X × Bool)}
    {q : Q} {xs : List (X × Bool)}
    (hprefix :
      D.prefixClosedQuotientSectionWordAlongList quotientSectionWord q xs)
    (hreduced : FreeGroup.IsReduced (quotientSectionWord q ++ xs)) :
    ∀ xb ∈ xs, xb.2 = true := by
  induction xs generalizing q with
  | nil =>
      intro xb hxb
      cases hxb
  | cons hd xs ih =>
      rcases hd with ⟨x, eps⟩
      cases eps
      · rcases hprefix with ⟨hstep, htail⟩
        have hbad :
            FreeGroup.IsReduced ([(x, true), (x, false)] :
              List (X × Bool)) := by
          refine hreduced.infix ?_
          refine ⟨quotientSectionWord (D.inverseTransition q x), xs, ?_⟩
          rw [hstep]
          simp only [inverseTransition_eq, List.append_assoc, List.cons_append, List.nil_append]
        rw [FreeGroup.isReduced_cons_cons] at hbad
        have hcontra := hbad.1 rfl
        simp only [Bool.true_eq_false] at hcontra
      · rcases hprefix with ⟨hstep, htail⟩
        have hreducedTail :
            FreeGroup.IsReduced
              (quotientSectionWord (D.transition q x) ++ xs) := by
          rw [hstep]
          simpa [List.append_assoc] using hreduced
        intro xb hxb
        simp only [List.mem_cons] at hxb
        rcases hxb with rfl | hmem
        · rfl
        · exact ih htail hreducedTail xb hmem

omit [DecidableEq X] in
/-- A reduced prefix-closed quotient-section word has only positive signed letters. -/
theorem quotientSectionWord_positive_of_prefixClosed_reduced
    {quotientSectionWord : Q → List (X × Bool)}
    (hOne : quotientSectionWord 1 = [])
    (hreduced : ∀ q : Q, FreeGroup.IsReduced (quotientSectionWord q))
    (hprefix :
      ∀ q : Q,
        D.prefixClosedQuotientSectionWordAlongList quotientSectionWord 1
          (quotientSectionWord q)) :
    ∀ q : Q, ∀ xb ∈ quotientSectionWord q, xb.2 = true := by
  intro q xb hxb
  have hreducedAppend :
      FreeGroup.IsReduced (quotientSectionWord 1 ++ quotientSectionWord q) := by
    simpa [hOne] using hreduced q
  exact
    D.snd_eq_true_of_prefixClosedQuotientSectionWordAlongList_of_isReduced_append
      (hprefix q) hreducedAppend xb hxb

end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
