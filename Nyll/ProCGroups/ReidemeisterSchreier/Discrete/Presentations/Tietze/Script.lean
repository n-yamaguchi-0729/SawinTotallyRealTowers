/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorDeletion

/-!
# Verified Tietze move scripts

`ElementaryTietzeMove` records genuine presentation transformations with
indexed source and target presentations.  `VerifiedTietzeScript` is the typed
sequence of those moves; it evaluates to a semantic
`PresentationEquivCertificate` and exposes an inspectable trace, move count,
and weighted cost.

Semantic equivalence constructors live in the Tietze core and operation
modules.  They are not re-exported here as a parallel family of “script”
wrappers.
-/

universe u

namespace ReidemeisterSchreier.Discrete.Presentations


/-- An inspectable, indexed Tietze move whose endpoints are determined by the
mathematical construction which produces its semantic certificate.

In particular, the generator moves do not accept an equivalence or a desired
conclusion as an extra field: their certificates are computed from the
generator-adjunction and generator-elimination constructions in this library. -/
inductive ElementaryTietzeMove :
    Presentation.{u} → Presentation.{u} → Type (u + 1) where
  /-- Replace a relator set by another set generating the same normal closure. -/
  | replaceRelators
      {X : Type u} {R S : Set (FreeGroup X)}
      (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
      (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
      ElementaryTietzeMove
        (Presentation.ofRelators R) (Presentation.ofRelators S)
  /-- Rename every generator through an equivalence of generator types. -/
  | renameGenerators
      {X Y : Type u} (R : Set (FreeGroup X)) (e : X ≃ Y) :
      ElementaryTietzeMove
        (Presentation.ofRelators R)
        (Presentation.ofRelators (FreeGroup.freeGroupCongr e '' R))
  /-- Adjoin generators together with relators identifying them with prescribed words. -/
  | adjoinGenerators
      {X Y : Type u} (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
      ElementaryTietzeMove
        (Presentation.ofRelators R)
        (Presentation.ofRelators (Presented.adjoinGeneratorsRelators R word))
  /-- Eliminate a family of generators by substituting their defining words. -/
  | substituteDefinedGenerators
      {X Y : Type u} (R : Set (FreeGroup (Sum X Y)))
      (word : Y → FreeGroup X) :
      ElementaryTietzeMove
        (Presentation.ofRelators
          (Presented.relatorsWithDefinedGenerators R word))
        (Presentation.ofRelators
          (Presented.relatorsAfterSubstitutingDefinedGenerators R word))
  /-- Delete a family of generators whose defining relators make them trivial. -/
  | deleteTrivialGenerators
      {X Y : Type u} (R : Set (FreeGroup (Sum X Y))) :
      ElementaryTietzeMove
        (Presentation.ofRelators (Presented.relatorsWithTrivialGenerators R))
        (Presentation.ofRelators
          (Presented.relatorsAfterDeletingTrivialGenerators R))
  /--
  Transport to a sum decomposition of the generator type and then substitute the defining words.
  -/
  | substituteDefinedGeneratorsAlongEquiv
      {Z X Y : Type u} (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
      (word : Y → FreeGroup X) :
      ElementaryTietzeMove
        (Presentation.ofRelators
          (Presented.relatorsWithDefinedGeneratorsAlongEquiv R e word))
        (Presentation.ofRelators
          (Presented.relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv R e word))
  /-- Transport to a sum decomposition and then delete the generators made trivial by relators. -/
  | deleteTrivialGeneratorsAlongEquiv
      {Z X Y : Type u} (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
      ElementaryTietzeMove
        (Presentation.ofRelators
          (Presented.relatorsWithTrivialGeneratorsAlongEquiv R e))
        (Presentation.ofRelators
          (Presented.relatorsAfterDeletingTrivialGeneratorsAlongEquiv R e))

namespace ElementaryTietzeMove

/-- Stable tags for script traces and cost functions. -/
inductive Kind where
  /-- A relator-set replacement. -/
  | replaceRelators
  /-- A renaming of generators. -/
  | renameGenerators
  /-- An adjunction of generators with defining relators. -/
  | adjoinGenerators
  /-- A substitution eliminating generators with specified defining words. -/
  | substituteDefinedGenerators
  /-- A deletion of generators made trivial by their defining relators. -/
  | deleteTrivialGenerators
deriving DecidableEq, Repr

/-- Inspect the mathematical kind of an elementary move. -/
def kind {P Q : Presentation.{u}} : ElementaryTietzeMove P Q → Kind
  | .replaceRelators _ _ => .replaceRelators
  | .renameGenerators _ _ => .renameGenerators
  | .adjoinGenerators _ _ => .adjoinGenerators
  | .substituteDefinedGenerators _ _ => .substituteDefinedGenerators
  | .deleteTrivialGenerators _ => .deleteTrivialGenerators
  | .substituteDefinedGeneratorsAlongEquiv _ _ _ => .substituteDefinedGenerators
  | .deleteTrivialGeneratorsAlongEquiv _ _ => .deleteTrivialGenerators

/-- Evaluate one indexed move using its source-producing semantic
construction. -/
def toCertificate {P Q : Presentation.{u}}
    (m : ElementaryTietzeMove P Q) : PresentationEquivCertificate P Q := by
  cases m with
  | replaceRelators hR_to_S hS_to_R =>
      exact (Presented.replaceRelatorsTietzeEquiv hR_to_S hS_to_R).toCertificate
  | renameGenerators R e =>
      exact (Presented.renameGeneratorsTietzeEquiv R e).toCertificate
  | adjoinGenerators R word =>
      exact (Presented.adjoinGeneratorsTietzeEquiv R word).toCertificate
  | substituteDefinedGenerators R word =>
      exact (Presented.substituteDefinedGeneratorsTietzeEquiv R word).toCertificate
  | deleteTrivialGenerators R =>
      exact (Presented.deleteTrivialGeneratorsTietzeEquiv R).toCertificate
  | substituteDefinedGeneratorsAlongEquiv R e word =>
      exact
        (Presented.substituteDefinedGeneratorsAlongEquivTietzeEquiv R e word).toCertificate
  | deleteTrivialGeneratorsAlongEquiv R e =>
      exact (Presented.deleteTrivialGeneratorsAlongEquivTietzeEquiv R e).toCertificate

end ElementaryTietzeMove

/-- A well-typed sequence of genuine Tietze moves.  The indexed intermediate
presentations make an ill-typed move chain unrepresentable. -/
inductive VerifiedTietzeScript :
    Presentation.{u} → Presentation.{u} → Type (u + 1) where
  /-- The empty script at a presentation. -/
  | nil (P : Presentation.{u}) : VerifiedTietzeScript P P
  /-- Prepend an elementary move to a verified script beginning at its target presentation. -/
  | cons {P Q R : Presentation.{u}}
      (head : ElementaryTietzeMove P Q)
      (tail : VerifiedTietzeScript Q R) : VerifiedTietzeScript P R

namespace VerifiedTietzeScript

/-- A one-move verified script. -/
def singleton {P Q : Presentation.{u}} (m : ElementaryTietzeMove P Q) :
    VerifiedTietzeScript P Q :=
  .cons m (.nil Q)

/-- A verified relator-replacement move. -/
def replaceRelators
    {X : Type u} {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    VerifiedTietzeScript
      (Presentation.ofRelators R) (Presentation.ofRelators S) :=
  singleton (.replaceRelators hR_to_S hS_to_R)

/-- Rename the complete generator family by an equivalence. -/
def renameGenerators
    {X Y : Type u} (R : Set (FreeGroup X)) (e : X ≃ Y) :
    VerifiedTietzeScript
      (Presentation.ofRelators R)
      (Presentation.ofRelators (FreeGroup.freeGroupCongr e '' R)) :=
  singleton (.renameGenerators R e)

/-- Adjoin a family of generators together with the defining words which make
the extension a Tietze equivalence. -/
def adjoinGenerators
    {X Y : Type u} (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
    VerifiedTietzeScript
      (Presentation.ofRelators R)
      (Presentation.ofRelators (Presented.adjoinGeneratorsRelators R word)) :=
  singleton (.adjoinGenerators R word)

/-- Eliminate a family of generators whose defining words have been included
in the relator family. -/
def substituteDefinedGenerators
    {X Y : Type u} (R : Set (FreeGroup (Sum X Y)))
    (word : Y → FreeGroup X) :
    VerifiedTietzeScript
      (Presentation.ofRelators (Presented.relatorsWithDefinedGenerators R word))
      (Presentation.ofRelators
        (Presented.relatorsAfterSubstitutingDefinedGenerators R word)) :=
  singleton (.substituteDefinedGenerators R word)

/-- Delete a family of generators carrying the relators `y = 1`. -/
def deleteTrivialGenerators
    {X Y : Type u} (R : Set (FreeGroup (Sum X Y))) :
    VerifiedTietzeScript
      (Presentation.ofRelators (Presented.relatorsWithTrivialGenerators R))
      (Presentation.ofRelators (Presented.relatorsAfterDeletingTrivialGenerators R)) :=
  singleton (.deleteTrivialGenerators R)

/-- Eliminate a family of defined generators after an explicit splitting of
an arbitrary generator type. -/
def substituteDefinedGeneratorsAlongEquiv
    {Z X Y : Type u} (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    VerifiedTietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithDefinedGeneratorsAlongEquiv R e word))
      (Presentation.ofRelators
        (Presented.relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv R e word)) :=
  singleton (.substituteDefinedGeneratorsAlongEquiv R e word)

/-- Delete trivial generators after an explicit splitting of an arbitrary
generator type. -/
def deleteTrivialGeneratorsAlongEquiv
    {Z X Y : Type u} (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    VerifiedTietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithTrivialGeneratorsAlongEquiv R e))
      (Presentation.ofRelators
        (Presented.relatorsAfterDeletingTrivialGeneratorsAlongEquiv R e)) :=
  singleton (.deleteTrivialGeneratorsAlongEquiv R e)

/-- Delete exactly the generators selected by a decidable predicate. -/
def deleteTrivialGeneratorsOfPredicate
    {Z : Type u} (R : Set (FreeGroup Z)) (delete : Z → Prop)
    [DecidablePred delete] :
    VerifiedTietzeScript
      (Presentation.ofRelators
        (Presented.relatorsWithTrivialGeneratorsOfPredicate R delete))
      (Presentation.ofRelators
        (Presented.relatorsAfterDeletingTrivialGeneratorsOfPredicate R delete)) :=
  deleteTrivialGeneratorsAlongEquiv R
    (X := Presented.GeneratorPartition.Kept delete)
    (Y := Presented.GeneratorPartition.Deleted delete)
    (Presented.GeneratorPartition.equiv delete)

/-- Concatenate two verified scripts. -/
def trans {P Q R : Presentation.{u}}
    (s : VerifiedTietzeScript P Q) (t : VerifiedTietzeScript Q R) :
    VerifiedTietzeScript P R :=
  match s with
  | .nil _ => t
  | .cons head tail => .cons head (tail.trans t)

/-- Evaluate a complete move sequence to its semantic certificate. -/
def toCertificate {P Q : Presentation.{u}}
    (s : VerifiedTietzeScript P Q) : PresentationEquivCertificate P Q :=
  match s with
  | .nil P => PresentationEquivCertificate.refl P
  | .cons head tail =>
      PresentationEquivCertificate.trans head.toCertificate tail.toCertificate

/-- The inspectable sequence of move kinds. -/
def trace {P Q : Presentation.{u}}
    (s : VerifiedTietzeScript P Q) : List ElementaryTietzeMove.Kind :=
  match s with
  | .nil _ => []
  | .cons head tail => head.kind :: tail.trace

/-- The number of elementary moves in a verified script. -/
def moveCount {P Q : Presentation.{u}} (s : VerifiedTietzeScript P Q) : ℕ :=
  s.trace.length

/-- A customizable additive script cost. -/
def cost {P Q : Presentation.{u}}
    (s : VerifiedTietzeScript P Q)
    (weight : ElementaryTietzeMove.Kind → ℕ) : ℕ :=
  (s.trace.map weight).sum

/-- The empty verified script has an empty move trace. -/
@[simp] theorem trace_nil (P : Presentation.{u}) :
    (VerifiedTietzeScript.nil P).trace = [] := rfl

/-- The trace of a script begins with the kind of its head move. -/
@[simp] theorem trace_cons
    {P Q R : Presentation.{u}} (head : ElementaryTietzeMove P Q)
    (tail : VerifiedTietzeScript Q R) :
    (VerifiedTietzeScript.cons head tail).trace = head.kind :: tail.trace := rfl

/-- A singleton script records exactly the kind of its sole move. -/
@[simp] theorem trace_singleton
    {P Q : Presentation.{u}} (move : ElementaryTietzeMove P Q) :
    (singleton move).trace = [move.kind] := rfl

/-- The empty verified script contains no moves. -/
@[simp] theorem moveCount_nil (P : Presentation.{u}) :
    (VerifiedTietzeScript.nil P).moveCount = 0 := rfl

/-- Prepending a move increases the length of a verified script by one. -/
@[simp] theorem moveCount_cons
    {P Q R : Presentation.{u}} (head : ElementaryTietzeMove P Q)
    (tail : VerifiedTietzeScript Q R) :
    (VerifiedTietzeScript.cons head tail).moveCount = tail.moveCount + 1 := by
  simp [moveCount, trace, Nat.add_comm]

/-- A singleton verified script contains one move. -/
@[simp] theorem moveCount_singleton
    {P Q : Presentation.{u}} (move : ElementaryTietzeMove P Q) :
    (singleton move).moveCount = 1 := rfl

/-- Concatenating verified scripts adds their move counts. -/
@[simp] theorem moveCount_trans
    {P Q R : Presentation.{u}} (s : VerifiedTietzeScript P Q)
    (t : VerifiedTietzeScript Q R) :
    (s.trans t).moveCount = s.moveCount + t.moveCount := by
  induction s with
  | nil => simp [trans, moveCount, trace]
  | cons head tail ih =>
      simp [trans, ih, Nat.add_assoc, Nat.add_comm]

/-- The empty verified script has zero cost for every weighting. -/
@[simp] theorem cost_nil
    (weight : ElementaryTietzeMove.Kind → ℕ) (P : Presentation.{u}) :
    (VerifiedTietzeScript.nil P).cost weight = 0 := rfl

/-- The cost of a nonempty script is the head move's weight plus the tail cost. -/
@[simp] theorem cost_cons
    (weight : ElementaryTietzeMove.Kind → ℕ)
    {P Q R : Presentation.{u}} (head : ElementaryTietzeMove P Q)
    (tail : VerifiedTietzeScript Q R) :
    (VerifiedTietzeScript.cons head tail).cost weight =
      weight head.kind + tail.cost weight := rfl

/-- The cost of a singleton script is the weight assigned to its sole move. -/
@[simp] theorem cost_singleton
    (weight : ElementaryTietzeMove.Kind → ℕ)
    {P Q : Presentation.{u}} (move : ElementaryTietzeMove P Q) :
    (singleton move).cost weight = weight move.kind := by
  simp [singleton]

end VerifiedTietzeScript

end ReidemeisterSchreier.Discrete.Presentations
