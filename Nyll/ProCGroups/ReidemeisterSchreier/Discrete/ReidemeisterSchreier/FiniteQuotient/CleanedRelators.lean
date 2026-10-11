/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.ReidemeisterSchreier.FiniteQuotient.CleanedTau

/-!
# Reidemeister Schreier / Discrete / Reidemeister Schreier / Finite Quotient / Cleaned Relators

This module removes relators attached to degenerate Schreier symbols, builds
the finite cleaned relator set, and records the remaining quotient-section
and augmented relator families.
-/


namespace ReidemeisterSchreier.Discrete

open ReidemeisterSchreier.Discrete.Presentations

variable {X Q : Type*} [Group Q] [Fintype Q]

namespace FiniteQuotientSchreierData

variable (D : FiniteQuotientSchreierData X Q)
variable [DecidableEq X]

/--
This is the relator family obtained by rewriting original relators and then deleting degenerate
Schreier generators.
-/
def cleanedSchreierRelators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    Set (FreeGroup D.NondegenerateSchreierSymbol) :=
  { z | ∃ q : Q, ∃ r ∈ R, z = D.cleanedTau q r }

/--
Membership in the cleaned Schreier relator set is characterized by a quotient element and an
original relator whose cleaned rewrite gives the word.
-/
theorem mem_cleanedSchreierRelators
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol]
    (q : Q) {r : FreeGroup X} (hr : r ∈ R) :
    D.cleanedTau q r ∈ D.cleanedSchreierRelators R :=
  ⟨q, r, hr, rfl⟩

/--
The cleaned Schreier relator finset contains the cleaned rewrites of the finite quotient
elements and original relators.
-/
noncomputable def cleanedSchreierRelatorFinset
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq (FreeGroup D.NondegenerateSchreierSymbol)]
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup D.NondegenerateSchreierSymbol) :=
  (Finset.univ : Finset Q).biUnion
    (fun q => R.image (fun r => D.cleanedTau q r))

/--
Membership in the cleaned Schreier relator finset is characterized by a quotient element and an
original relator whose cleaned rewrite gives the word.
-/
@[simp]
theorem mem_cleanedSchreierRelatorFinset
    {D : FiniteQuotientSchreierData X Q}
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq (FreeGroup D.NondegenerateSchreierSymbol)]
    {R : Finset (FreeGroup X)} {z : FreeGroup D.NondegenerateSchreierSymbol} :
    z ∈ D.cleanedSchreierRelatorFinset R ↔
      z ∈ D.cleanedSchreierRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  simp only [cleanedSchreierRelatorFinset, Finset.mem_biUnion, Finset.mem_univ,
      Finset.mem_image, eq_comm,
  true_and, cleanedSchreierRelators, SetLike.setOfPred_mem_eq, SetLike.mem_coe, Set.mem_ofPred_eq]

/-- Coercing the cleaned Schreier relator finset gives the cleaned Schreier relator set. -/
@[simp]
theorem coe_cleanedSchreierRelatorFinset
    [DecidablePred D.IsDegenerateSchreierSymbol]
    [DecidableEq (FreeGroup D.NondegenerateSchreierSymbol)]
    (R : Finset (FreeGroup X)) :
    ({z | z ∈ D.cleanedSchreierRelatorFinset R} :
      Set (FreeGroup D.NondegenerateSchreierSymbol)) =
      D.cleanedSchreierRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  ext z
  simp only [mem_cleanedSchreierRelatorFinset, SetLike.setOfPred_mem_eq, Set.ofPred_mem_eq]

/--
The relators after deleting degenerate Schreier generators are exactly the cleaned Schreier
relators.
-/
theorem presentationRelatorsAfterDeletingDegenerate_eq_cleaned
    (R : Set (FreeGroup X))
    [DecidablePred D.IsDegenerateSchreierSymbol] :
    D.presentationRelatorsAfterDeletingDegenerateSchreierGenerators R =
      D.cleanedSchreierRelators R := by
  ext z
  change z ∈
      Presented.trivializeGeneratorsHom
          D.NondegenerateSchreierSymbol D.DegenerateSchreierSymbol ''
        (FreeGroup.freeGroupCongr
            (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol) ''
          D.schreierRelators R) ↔
    z ∈ D.cleanedSchreierRelators R
  constructor
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    rcases hx with ⟨q, r, hr, rfl⟩
    exact ⟨q, r, hr, rfl⟩
  · rintro ⟨q, r, hr, rfl⟩
    exact
      ⟨FreeGroup.freeGroupCongr
          (Presented.GeneratorPartition.equiv D.IsDegenerateSchreierSymbol)
          (D.tau q r),
        ⟨D.tau q r, ⟨q, r, hr, rfl⟩, rfl⟩, rfl⟩

/--
Relators forcing the chosen quotient representatives to rewrite to the empty word. These are
automatic for a prefix-closed Schreier transversal, but are useful for arbitrary finite quotient
sections.
-/
def quotientSectionRelators :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  { q | ∃ s : Q, q = D.tau 1 (D.quotientSection s) }

/--
The augmented presentation relators combine quotient-section relators with the presentation
relators.
-/
def augmentedPresentationRelators (R : Set (FreeGroup X)) :
    Set (FreeGroup (FiniteSchreierSymbol X Q)) :=
  D.presentationRelators R ∪ D.quotientSectionRelators

/-- A finite set enumerating the finite-quotient Schreier relators. -/
noncomputable def schreierRelatorFinset
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact Finset.univ.biUnion (fun s : Q => R.image (D.tau s))

/--
Membership in the Schreier-relator finset is equivalent to membership in the finite-quotient
Schreier relator set.
-/
theorem mem_schreierRelatorFinset
    {D : FiniteQuotientSchreierData X Q}
    {R : Finset (FreeGroup X)}
    {z : FreeGroup (FiniteSchreierSymbol X Q)} :
    z ∈ D.schreierRelatorFinset R ↔
      z ∈ D.schreierRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  classical
  simp only [schreierRelatorFinset, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image,
      eq_comm, true_and,
  schreierRelators, SetLike.setOfPred_mem_eq, SetLike.mem_coe, Set.mem_ofPred_eq]

/-- A finite set enumerating the degenerate finite-quotient Schreier relators. -/
noncomputable def degenerateSchreierRelatorFinset [Fintype X] :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact (((Finset.univ : Finset Q).product (Finset.univ : Finset X)).filter
    (fun z =>
      D.quotientSection (D.transition z.1 z.2) =
        D.quotientSection z.1 * FreeGroup.of z.2)).image
          (fun z => FreeGroup.of z)

/--
Membership in the degenerate-Schreier-relator finset is equivalent to membership in the
degenerate Schreier relator set.
-/
theorem mem_degenerateSchreierRelatorFinset [Fintype X]
    {D : FiniteQuotientSchreierData X Q}
    {z : FreeGroup (FiniteSchreierSymbol X Q)} :
    z ∈ D.degenerateSchreierRelatorFinset ↔
      z ∈ D.degenerateSchreierRelators := by
  classical
  simp only [degenerateSchreierRelatorFinset, transition_eq, eq_comm, Finset.product_eq_sprod,
  Finset.univ_product_univ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      Prod.exists,
  degenerateSchreierRelators, Set.mem_ofPred_eq]

/-- A finite set enumerating the finite-quotient presentation relators. -/
noncomputable def presentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact D.schreierRelatorFinset R ∪ D.degenerateSchreierRelatorFinset

/--
Membership in the presentation-relator finset is equivalent to membership in the finite-quotient
presentation relator set.
-/
theorem mem_presentationRelatorFinset [Fintype X]
    {D : FiniteQuotientSchreierData X Q}
    {R : Finset (FreeGroup X)}
    {z : FreeGroup (FiniteSchreierSymbol X Q)} :
    z ∈ D.presentationRelatorFinset R ↔
      z ∈ D.presentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  classical
  simp only [presentationRelatorFinset, Finset.mem_union, mem_schreierRelatorFinset,
      SetLike.setOfPred_mem_eq,
  mem_degenerateSchreierRelatorFinset, presentationRelators, Set.mem_union]

/-- The presentation-relator finset coerces to the finite-quotient presentation relator set. -/
theorem coe_presentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    ({z | z ∈ D.presentationRelatorFinset R} :
      Set (FreeGroup (FiniteSchreierSymbol X Q))) =
      D.presentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  ext z
  exact D.mem_presentationRelatorFinset (R := R) (z := z)

/--
The quotient-section relator finset contains the finite relators killing the chosen
quotient-section words.
-/
noncomputable def quotientSectionRelatorFinset :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact Finset.univ.image (fun s : Q => D.tau 1 (D.quotientSection s))

/--
Membership in the quotient-section relator finset is characterized by a quotient element whose
section word is being killed.
-/
theorem mem_quotientSectionRelatorFinset
    {D : FiniteQuotientSchreierData X Q}
    {z : FreeGroup (FiniteSchreierSymbol X Q)} :
    z ∈ D.quotientSectionRelatorFinset ↔
      z ∈ D.quotientSectionRelators := by
  classical
  simp only [quotientSectionRelatorFinset, Finset.mem_image, Finset.mem_univ, eq_comm, true_and,
  quotientSectionRelators, Set.mem_ofPred_eq]

/--
The finite augmented presentation relator set combines quotient-section relators with the finite
presentation relators.
-/
noncomputable def augmentedPresentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    Finset (FreeGroup (FiniteSchreierSymbol X Q)) := by
  classical
  exact D.presentationRelatorFinset R ∪ D.quotientSectionRelatorFinset

/--
Membership in the augmented presentation relator finset is membership in either the
quotient-section relators or the presentation relator finset.
-/
theorem mem_augmentedPresentationRelatorFinset [Fintype X]
    {D : FiniteQuotientSchreierData X Q}
    {R : Finset (FreeGroup X)}
    {z : FreeGroup (FiniteSchreierSymbol X Q)} :
    z ∈ D.augmentedPresentationRelatorFinset R ↔
      z ∈ D.augmentedPresentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  classical
  simp only [augmentedPresentationRelatorFinset, Finset.mem_union, mem_presentationRelatorFinset,
  SetLike.setOfPred_mem_eq, mem_quotientSectionRelatorFinset, augmentedPresentationRelators,
      Set.mem_union]

/--
Coercing the augmented presentation relator finset gives the augmented presentation relator set.
-/
theorem coe_augmentedPresentationRelatorFinset [Fintype X]
    (R : Finset (FreeGroup X)) :
    ({z | z ∈ D.augmentedPresentationRelatorFinset R} :
      Set (FreeGroup (FiniteSchreierSymbol X Q))) =
      D.augmentedPresentationRelators ({r | r ∈ R} : Set (FreeGroup X)) := by
  ext z
  exact D.mem_augmentedPresentationRelatorFinset (R := R) (z := z)

end FiniteQuotientSchreierData

end ReidemeisterSchreier.Discrete
