/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.KernelQuotient
import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.Tau

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Cleaned Symbols

This module separates degenerate Schreier symbols from genuine generators and
sets up the relator families needed to delete the trivial generators from the
finite-quotient presentation.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

omit [DecidableEq X] in
/--
Predicate saying that a finite Schreier symbol is degenerate and should be deleted from the
cleaned presentation.
-/
def IsDegenerateSchreierSymbol (z : FiniteSchreierSymbol X Q) : Prop :=
  D.quotientSection (D.transition z.1 z.2) =
    D.quotientSection z.1 * FreeGroup.of z.2

omit [DecidableEq X] in
/--
The set of degenerate finite-quotient Schreier relators killed when deleting degenerate symbols.
-/
def degenerateSchreierRelators :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  { q | ∃ s : Q, ∃ x : X,
      D.quotientSection (D.transition s x) = D.quotientSection s * FreeGroup.of x ∧
        q = FreeGroup.of (s, x) }

/--
The finite-quotient presentation relators are the Schreier relators together with the degenerate
Schreier-generator relators.
-/
def presentationRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  D.schreierRelators R ∪ D.degenerateSchreierRelators

omit [DecidableEq X] in
/-- The type of finite Schreier symbols kept after deleting degenerate symbols. -/
abbrev NondegenerateSchreierSymbol :=
  Presented.GeneratorPartition.Kept D.IsDegenerateSchreierSymbol

omit [DecidableEq X] in
/-- The type of finite Schreier symbols marked for deletion as degenerate. -/
abbrev DegenerateSchreierSymbol :=
  Presented.GeneratorPartition.Deleted D.IsDegenerateSchreierSymbol

omit [DecidableEq X] in
/--
The trivial-generator relators selected by the degeneracy predicate are exactly the degenerate
Schreier relators.
-/
theorem trivialGeneratorRelatorsOfPredicate_isDegenerateSchreierSymbol
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Presented.trivialGeneratorRelatorsOfPredicate D.IsDegenerateSchreierSymbol =
      D.degenerateSchreierRelators := by
  have hInverse (z : D.DegenerateSchreierSymbol) :
      (FreeGroup.freeGroupCongr
          (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol)).symm
          (FreeGroup.of (Sum.inr z)) = FreeGroup.of z.1 := by
    rw [FreeGroup.freeGroupCongr_symm, FreeGroup.freeGroupCongr_apply, FreeGroup.map.of]
    exact congrArg
      (FreeGroup.of : FiniteSchreierSymbol X Q → FreeGroup (FiniteSchreierSymbol X Q))
      (Presented.GeneratorPartition.equiv_symm_inr D.IsDegenerateSchreierSymbol z)
  ext q
  constructor
  · intro hq
    rcases hq with ⟨p, hp, hpq⟩
    rcases hp with ⟨y, rfl⟩
    rcases y with ⟨⟨s, x⟩, hy⟩
    refine ⟨s, x, hy, ?_⟩
    rw [← hpq]
    exact hInverse (⟨(s, x), hy⟩ : D.DegenerateSchreierSymbol)
  · rintro ⟨s, x, hdeg, rfl⟩
    refine ⟨FreeGroup.of (Sum.inr
      (⟨(s, x), hdeg⟩ : D.DegenerateSchreierSymbol)), ?_, ?_⟩
    · exact ⟨⟨(s, x), hdeg⟩, rfl⟩
    · exact hInverse (⟨(s, x), hdeg⟩ : D.DegenerateSchreierSymbol)

/--
Adding trivial-generator relators for degenerate Schreier symbols gives the presentation
relators.
-/
theorem relatorsWithTrivialGeneratorsOfPredicate_isDegenerateSchreierSymbol
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Presented.relatorsWithTrivialGeneratorsOfPredicate
        (D.schreierRelators R) D.IsDegenerateSchreierSymbol =
      D.presentationRelators R := by
  change D.schreierRelators R ∪
      Presented.trivialGeneratorRelatorsOfPredicate D.IsDegenerateSchreierSymbol =
    D.schreierRelators R ∪ D.degenerateSchreierRelators
  rw [D.trivialGeneratorRelatorsOfPredicate_isDegenerateSchreierSymbol]

/--
The raw finite Reidemeister--Schreier relators after deleting the degenerate Schreier generators
with relators \(s(q,x)=1\).
-/
def presentationRelatorsAfterDeletingDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.NondegenerateSchreierSymbol) :=
  Presented.relatorsAfterDeletingTrivialGeneratorsOfPredicate
    (D.schreierRelators R) D.IsDegenerateSchreierSymbol

/--
Deleting degenerate finite Schreier generators gives a Tietze equivalence with the cleaned
presentation.
-/
def deleteDegenerateSchreierGeneratorsScript
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    VerifiedTietzeScript
      (Presentation.ofRelators (D.presentationRelators R))
      (Presentation.ofRelators
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R)) := by
  let hRelators :=
    D.relatorsWithTrivialGeneratorsOfPredicate_isDegenerateSchreierSymbol R
  exact
    (VerifiedTietzeScript.replaceRelators
      (fun r hr => RelatorEquivalent.of_mem (by simpa only [hRelators] using hr))
      (fun r hr => RelatorEquivalent.of_mem (by simpa only [hRelators] using hr))).trans
      (VerifiedTietzeScript.deleteTrivialGeneratorsOfPredicate
        (D.schreierRelators R) D.IsDegenerateSchreierSymbol)

/-- The cleaned-symbol construction first identifies the proved-equal relator
families and then performs one indexed generator-deletion move.  This theorem
makes the maintained concrete consumer visible to trace and cost clients. -/
theorem deleteDegenerateSchreierGeneratorsScript_trace
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    (D.deleteDegenerateSchreierGeneratorsScript R).trace =
      [ElementaryTietzeMove.Kind.replaceRelators,
        ElementaryTietzeMove.Kind.deleteTrivialGenerators] := by
  simp [deleteDegenerateSchreierGeneratorsScript,
    VerifiedTietzeScript.replaceRelators,
    VerifiedTietzeScript.deleteTrivialGeneratorsOfPredicate,
    VerifiedTietzeScript.deleteTrivialGeneratorsAlongEquiv,
    VerifiedTietzeScript.singleton, VerifiedTietzeScript.trans,
    VerifiedTietzeScript.trace,
    ElementaryTietzeMove.kind]

/-- The deletion script's weighted cost is the cost of replacing relators plus the weighted
cost of deleting each degenerate Schreier generator. -/
theorem deleteDegenerateSchreierGeneratorsScript_cost
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (weight : ElementaryTietzeMove.Kind → ℕ) :
    (D.deleteDegenerateSchreierGeneratorsScript R).cost weight =
      weight ElementaryTietzeMove.Kind.replaceRelators +
        weight ElementaryTietzeMove.Kind.deleteTrivialGenerators := by
  simp [deleteDegenerateSchreierGeneratorsScript,
    VerifiedTietzeScript.replaceRelators,
    VerifiedTietzeScript.deleteTrivialGeneratorsOfPredicate,
    VerifiedTietzeScript.deleteTrivialGeneratorsAlongEquiv,
    VerifiedTietzeScript.singleton, VerifiedTietzeScript.trans,
    VerifiedTietzeScript.cost,
    VerifiedTietzeScript.trace, ElementaryTietzeMove.kind]

/--
Deleting degenerate finite Schreier generators produces the cleaned presentation on
nondegenerate Schreier symbols.
-/
noncomputable def deleteDegenerateSchreierGenerators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    PresentedGroup (D.presentationRelators R) ≃*
      PresentedGroup
        (D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R) :=
  (D.deleteDegenerateSchreierGeneratorsScript R).toCertificate.presentedEquiv

/--
The homomorphism that deletes degenerate finite Schreier generators. A nondegenerate generator
is kept, and a degenerate generator is sent to \(1\).
-/
def deleteDegenerateSchreierGeneratorHom
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    FreeGroup (FiniteSchreierSymbol X Q) →*
      FreeGroup D.NondegenerateSchreierSymbol :=
  (Presented.trivializeGeneratorsHom
      D.NondegenerateSchreierSymbol D.DegenerateSchreierSymbol).comp
    (FreeGroup.freeGroupCongr
      (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol))

omit [DecidableEq X] in
/--
The generator-deletion homomorphism sends a nondegenerate finite Schreier generator to the
corresponding nondegenerate generator.
-/
@[simp]
theorem deleteDegenerateSchreierGeneratorHom_of_not_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : ¬ D.IsDegenerateSchreierSymbol z) :
    D.deleteDegenerateSchreierGeneratorHom (FreeGroup.of z) =
      FreeGroup.of (⟨z, hz⟩ : D.NondegenerateSchreierSymbol) := by
  simp only [deleteDegenerateSchreierGeneratorHom, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
      Function.comp_apply,
  FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
  Presented.GeneratorPartition.equiv_apply_of_not_delete D.IsDegenerateSchreierSymbol hz]
  exact Presented.trivializeGeneratorsHom_inl
    (X := D.NondegenerateSchreierSymbol)
    (Y := D.DegenerateSchreierSymbol)
    (⟨z, hz⟩ : D.NondegenerateSchreierSymbol)

omit [DecidableEq X] in
/--
The generator-deletion homomorphism sends a degenerate finite Schreier generator to the
identity.
-/
@[simp]
theorem deleteDegenerateSchreierGeneratorHom_of_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : D.IsDegenerateSchreierSymbol z) :
    D.deleteDegenerateSchreierGeneratorHom (FreeGroup.of z) = 1 := by
  simp only [deleteDegenerateSchreierGeneratorHom, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
      Function.comp_apply,
  FreeGroup.freeGroupCongr_apply, FreeGroup.map.of,
  Presented.GeneratorPartition.equiv_apply_of_delete D.IsDegenerateSchreierSymbol hz]
  exact Presented.trivializeGeneratorsHom_inr
    (X := D.NondegenerateSchreierSymbol)
    (Y := D.DegenerateSchreierSymbol)
    (⟨z, hz⟩ : D.DegenerateSchreierSymbol)

omit [DecidableEq X] in
/-- A degenerate Schreier symbol evaluates to the identity. -/
theorem symbolEval_eq_one_of_isDegenerateSchreierSymbol
    {z : FiniteSchreierSymbol X Q} (hz : D.IsDegenerateSchreierSymbol z) :
    D.symbolEval z = 1 := by
  rcases z with ⟨q, x⟩
  simp only [IsDegenerateSchreierSymbol, transition_eq, symbolEval, schreierGenerator] at hz ⊢
  rw [hz]
  group

/-- The evaluation map on the nondegenerate finite Schreier generators. -/
def nondegenerateSymbolEval
    (z : D.NondegenerateSchreierSymbol) : FreeGroup X :=
  D.symbolEval z.1

/-- The evaluation homomorphism on nondegenerate finite Schreier symbols. -/
def nondegenerateSymbolEvalHom :
    FreeGroup D.NondegenerateSchreierSymbol →* FreeGroup X :=
  FreeGroup.lift D.nondegenerateSymbolEval

omit [DecidableEq X] in
/--
Evaluating after deleting degenerate Schreier generators agrees with ordinary symbol evaluation.
-/
theorem nondegenerateSymbolEvalHom_deleteDegenerateSchreierGeneratorHom
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (w : FreeGroup (FiniteSchreierSymbol X Q)) :
    D.nondegenerateSymbolEvalHom
        (D.deleteDegenerateSchreierGeneratorHom w) =
      D.symbolEvalHom w := by
  let F : FreeGroup (FiniteSchreierSymbol X Q) →* FreeGroup X :=
    D.nondegenerateSymbolEvalHom.comp D.deleteDegenerateSchreierGeneratorHom
  have hF : F = D.symbolEvalHom := by
    ext z
    by_cases hz : D.IsDegenerateSchreierSymbol z
    · simp only [MonoidHom.coe_comp, Function.comp_apply,
        D.deleteDegenerateSchreierGeneratorHom_of_degenerate hz,
  map_one, symbolEvalHom_of, D.symbolEval_eq_one_of_isDegenerateSchreierSymbol hz, F]
    · simp only [MonoidHom.coe_comp, Function.comp_apply,
        D.deleteDegenerateSchreierGeneratorHom_of_not_degenerate hz,
        symbolEvalHom_of, F]
      exact FreeGroup.lift_apply_of (f := D.nondegenerateSymbolEval)
        (x := (⟨z, hz⟩ : D.NondegenerateSchreierSymbol))
  exact congrArg (fun f : FreeGroup (FiniteSchreierSymbol X Q) →* FreeGroup X => f w) hF

/-- A single finite Schreier generator after deleting degenerate generators. -/
def cleanedSchreierSymbolWord
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (z : FiniteSchreierSymbol X Q) :
    FreeGroup D.NondegenerateSchreierSymbol :=
  if hz : D.IsDegenerateSchreierSymbol z then
    1
  else
    FreeGroup.of (⟨z, hz⟩ : D.NondegenerateSchreierSymbol)

omit [DecidableEq X] in
/-- A degenerate Schreier symbol is deleted by the cleaned Schreier-symbol word map. -/
@[simp]
theorem cleanedSchreierSymbolWord_of_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : D.IsDegenerateSchreierSymbol z) :
    D.cleanedSchreierSymbolWord z = 1 := by
  simp only [cleanedSchreierSymbolWord, hz, ↓reduceDIte]

omit [DecidableEq X] in
/--
A nondegenerate Schreier symbol is kept as the corresponding generator by the cleaned
Schreier-symbol word map.
-/
@[simp]
theorem cleanedSchreierSymbolWord_of_not_degenerate
    [DecidablePred D.IsDegenerateSchreierSymbol]
    {z : FiniteSchreierSymbol X Q} (hz : ¬ D.IsDegenerateSchreierSymbol z) :
    D.cleanedSchreierSymbolWord z =
      FreeGroup.of (⟨z, hz⟩ : D.NondegenerateSchreierSymbol) := by
  simp only [cleanedSchreierSymbolWord, hz, ↓reduceDIte]
  congr

omit [DecidableEq X] in
/--
The generator-deletion homomorphism sends a finite Schreier generator to its cleaned
Schreier-symbol word.
-/
@[simp]
theorem deleteDegenerateSchreierGeneratorHom_of
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (z : FiniteSchreierSymbol X Q) :
    D.deleteDegenerateSchreierGeneratorHom (FreeGroup.of z) =
      D.cleanedSchreierSymbolWord z := by
  by_cases hz : D.IsDegenerateSchreierSymbol z
  · exact (D.deleteDegenerateSchreierGeneratorHom_of_degenerate hz).trans
      (D.cleanedSchreierSymbolWord_of_degenerate hz).symm
  · exact (D.deleteDegenerateSchreierGeneratorHom_of_not_degenerate hz).trans
      (D.cleanedSchreierSymbolWord_of_not_degenerate hz).symm


end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
