/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.Core

/-!
# Reidemeister Schreier / Discrete / Presentations / Tietze / Relator Replacement

This module supplies semantic presented-group equivalences for replacing
relators: equal normal closures, mutual relator maps, generator maps, and
compositions of these transformations.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

namespace Presented

variable {X Y : Type*}

/-- The identity equivalence of a presented group. -/
noncomputable def refl (R : Set (FreeGroup X)) :
    PresentedGroup R ≃* PresentedGroup R :=
  MulEquiv.refl (PresentedGroup R)

/-- Reverse an equivalence between two presented groups. -/
noncomputable def symm
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (e : PresentedGroup R ≃* PresentedGroup S) :
    PresentedGroup S ≃* PresentedGroup R :=
  e.symm

/-- Compose equivalences of presented groups through an intermediate presentation. -/
noncomputable def trans
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)} {Z : Type*}
    {T : Set (FreeGroup Z)}
    (e₁ : PresentedGroup R ≃* PresentedGroup S)
    (e₂ : PresentedGroup S ≃* PresentedGroup T) :
    PresentedGroup R ≃* PresentedGroup T :=
  e₁.trans e₂

/-- Mutual relator-quotient map data induces an equivalence between the two presented groups. -/
noncomputable def ofMutualMapData
    (R : Set (FreeGroup X)) (S : Set (FreeGroup Y))
    (D : RelatorQuotientMutualMapData R S) :
    PresentedGroup R ≃* PresentedGroup S :=
  quotientEquivOfRelatorQuotientMutualMapData R S D

/-- A Tietze equivalence induces an isomorphism between the corresponding presented groups. -/
noncomputable def ofTietzeEquiv
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (D : TietzeEquiv R S) :
    PresentedGroup R ≃* PresentedGroup S :=
  D.presentedEquiv

/--
Equal normal closures give a Tietze equivalence between presentations with the same generators.
-/
noncomputable def ofNormalClosureEq
    {R S : Set (FreeGroup X)}
    (h : Subgroup.normalClosure R = Subgroup.normalClosure S) :
    PresentedGroup R ≃* PresentedGroup S :=
  QuotientGroup.congr
    (Subgroup.normalClosure R)
    (Subgroup.normalClosure S)
    (MulEquiv.refl (FreeGroup X))
    (by simpa using h)

/--
Compatible generator maps in both directions induce an equivalence between the two presented
groups.
-/
noncomputable def ofGeneratorMaps
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        FreeGroup.lift toGenerator r ∈ Subgroup.normalClosure S)
    (hS :
      ∀ s ∈ S,
        FreeGroup.lift invGenerator s ∈ Subgroup.normalClosure R)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    PresentedGroup R ≃* PresentedGroup S :=
  (TietzeEquiv.ofGeneratorMaps
    toGenerator invGenerator hR hS hinv_to hto_inv).presentedEquiv

/--
Generator maps that preserve relators up to relator equivalence induce the corresponding
presented-group map.
-/
noncomputable def ofGeneratorMapsRelatorEquivalent
    {R : Set (FreeGroup X)} {S : Set (FreeGroup Y)}
    (toGenerator : X → FreeGroup Y)
    (invGenerator : Y → FreeGroup X)
    (hR :
      ∀ r ∈ R,
        RelatorEquivalent S (FreeGroup.lift toGenerator r) 1)
    (hS :
      ∀ s ∈ S,
        RelatorEquivalent R (FreeGroup.lift invGenerator s) 1)
    (hinv_to :
      ∀ x : X,
        RelatorEquivalent R
          (FreeGroup.lift invGenerator (toGenerator x))
          (FreeGroup.of x))
    (hto_inv :
      ∀ y : Y,
        RelatorEquivalent S
          (FreeGroup.lift toGenerator (invGenerator y))
          (FreeGroup.of y)) :
    PresentedGroup R ≃* PresentedGroup S :=
  (TietzeEquiv.ofGeneratorMapsRelatorEquivalent
    toGenerator invGenerator hR hS hinv_to hto_inv).presentedEquiv

/-- Replace a family of relators by equivalent relators in a presented group. -/
noncomputable def replaceRelators
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    PresentedGroup R ≃* PresentedGroup S :=
  ofNormalClosureEq (normalClosure_eq_of_relatorEquivalent hR_to_S hS_to_R)

/--
Replacing the relator set by another set with the same normal closure is a Tietze equivalence.
-/
def replaceRelatorsTietzeEquiv
    {R S : Set (FreeGroup X)}
    (hR_to_S : ∀ r ∈ R, RelatorEquivalent S r 1)
    (hS_to_R : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeEquiv R S :=
  TietzeEquiv.ofRelatorEquivalent hR_to_S hS_to_R

/-- Replace one relator by an equivalent relator in a presented group. -/
noncomputable def replaceRelator
    {R : Set (FreeGroup X)} {oldRelator newRelator : FreeGroup X}
    (holdRelator :
      RelatorEquivalent (insert newRelator (R \ {oldRelator})) oldRelator 1)
    (hnewRelator : RelatorEquivalent R newRelator 1) :
    PresentedGroup R ≃*
      PresentedGroup (insert newRelator (R \ {oldRelator})) :=
  replaceRelators
    (S := insert newRelator (R \ {oldRelator}))
    (by
      intro r hr
      by_cases hrold : r = oldRelator
      · simpa [hrold] using holdRelator
      · exact RelatorEquivalent.of_mem
          (R := insert newRelator (R \ {oldRelator}))
          (Or.inr ⟨hr, by simpa [Set.mem_singleton_iff] using hrold⟩))
    (by
      intro s hs
      rcases hs with rfl | hs
      · exact hnewRelator
      · exact RelatorEquivalent.of_mem (R := R) hs.1)

/-- Replacing one relator by another without changing the normal closure is a Tietze equivalence. -/
def replaceRelatorTietzeEquiv
    {R : Set (FreeGroup X)} {oldRelator newRelator : FreeGroup X}
    (holdRelator :
      RelatorEquivalent (insert newRelator (R \ {oldRelator})) oldRelator 1)
    (hnewRelator : RelatorEquivalent R newRelator 1) :
    TietzeEquiv R (insert newRelator (R \ {oldRelator})) :=
  replaceRelatorsTietzeEquiv
    (S := insert newRelator (R \ {oldRelator}))
    (by
      intro r hr
      by_cases hrold : r = oldRelator
      · simpa [hrold] using holdRelator
      · exact RelatorEquivalent.of_mem
          (R := insert newRelator (R \ {oldRelator}))
          (Or.inr ⟨hr, by simpa [Set.mem_singleton_iff] using hrold⟩))
    (by
      intro s hs
      rcases hs with rfl | hs
      · exact hnewRelator
      · exact RelatorEquivalent.of_mem (R := R) hs.1)

/-- Adjoining relators already contained in the original normal closure does not change it. -/
theorem normalClosure_union_eq_left_of_subset
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    Subgroup.normalClosure (R ∪ S) = Subgroup.normalClosure R := by
  apply normalClosure_eq_of_subset_normalClosure
  · intro x hx
    rcases hx with hx | hx
    · exact Subgroup.subset_normalClosure hx
    · exact hS hx
  · intro x hx
    exact Subgroup.subset_normalClosure (Or.inl hx)

/--
Removing relators already contained in the normal closure of the remaining relators does not
change that normal closure.
-/
theorem normalClosure_sdiff_eq_of_subset
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    Subgroup.normalClosure R = Subgroup.normalClosure (R \ D) := by
  apply normalClosure_eq_of_subset_normalClosure
  · intro r hr
    by_cases hd : r ∈ D
    · exact hD r hd hr
    · exact Subgroup.subset_normalClosure ⟨hr, hd⟩
  · intro r hr
    exact Subgroup.subset_normalClosure hr.1

/--
Adding a family of redundant relators to a presented group does not change the presented group.
-/
noncomputable def addRedundantRelators
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    PresentedGroup (R ∪ S) ≃* PresentedGroup R :=
  ofNormalClosureEq (normalClosure_union_eq_left_of_subset hS)

/-- Adding redundant relators preserves relator equivalence in the presented group. -/
noncomputable def addRedundantRelatorsRelatorEquivalent
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    PresentedGroup (R ∪ S) ≃* PresentedGroup R :=
  addRedundantRelators
    (R := R) (S := S)
    (fun s hs => RelatorEquivalent.mem_normalClosure_of_eq_one (hS s hs))

/-- Adding a set of relators already in the normal closure is a Tietze equivalence. -/
def addRedundantRelatorsTietzeEquiv
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    TietzeEquiv (R ∪ S) R :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_union_eq_left_of_subset hS)

/-- Adding redundant relators gives a Tietze equivalence of presentations. -/
def addRedundantRelatorsRelatorEquivalentTietzeEquiv
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    TietzeEquiv (R ∪ S) R :=
  addRedundantRelatorsTietzeEquiv
    (R := R) (S := S)
    (fun s hs => RelatorEquivalent.mem_normalClosure_of_eq_one (hS s hs))

/-- Remove a previously added family of redundant relators from a presented group. -/
noncomputable def addRedundantRelatorsInverse
    {R S : Set (FreeGroup X)}
    (hS : S ⊆ Subgroup.normalClosure R) :
    PresentedGroup R ≃* PresentedGroup (R ∪ S) :=
  (addRedundantRelators (R := R) (S := S) hS).symm

/-- The inverse direction after adding redundant relators preserves relator equivalence. -/
noncomputable def addRedundantRelatorsRelatorEquivalentInverse
    {R S : Set (FreeGroup X)}
    (hS : ∀ s ∈ S, RelatorEquivalent R s 1) :
    PresentedGroup R ≃* PresentedGroup (R ∪ S) :=
  (addRedundantRelatorsRelatorEquivalent (R := R) (S := S) hS).symm

/-- Remove a subset of relators already generated by the remaining relators. -/
noncomputable def removeRelatorSubset
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    PresentedGroup R ≃* PresentedGroup (R \ D) :=
  ofNormalClosureEq (normalClosure_sdiff_eq_of_subset hD)

/--
Removing a relator subset preserves relator equivalence under the stated normal-closure
hypothesis.
-/
noncomputable def removeRelatorSubsetRelatorEquivalent
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    PresentedGroup R ≃* PresentedGroup (R \ D) :=
  removeRelatorSubset
    (R := R) (D := D)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))

/--
Removing a subset of redundant relators is a Tietze equivalence when the normal closure is
unchanged.
-/
def removeRelatorSubsetTietzeEquiv
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    TietzeEquiv R (R \ D) :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_sdiff_eq_of_subset hD)

/-- Removing a redundant relator subset gives a Tietze equivalence of presentations. -/
def removeRelatorSubsetRelatorEquivalentTietzeEquiv
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    TietzeEquiv R (R \ D) :=
  removeRelatorSubsetTietzeEquiv
    (R := R) (D := D)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))

/-- Add back a relator subset previously removed as redundant. -/
noncomputable def removeRelatorSubsetInverse
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure (R \ D)) :
    PresentedGroup (R \ D) ≃* PresentedGroup R :=
  (removeRelatorSubset (R := R) (D := D) hD).symm

/-- The inverse direction after removing a relator subset preserves relator equivalence. -/
noncomputable def removeRelatorSubsetRelatorEquivalentInverse
    {R D : Set (FreeGroup X)}
    (hD : ∀ d ∈ D, d ∈ R → RelatorEquivalent (R \ D) d 1) :
    PresentedGroup (R \ D) ≃* PresentedGroup R :=
  (removeRelatorSubsetRelatorEquivalent (R := R) (D := D) hD).symm

/--
Replace a whole subfamily \(D\) of relators by a new family \(E\). Relators outside \(D\) are
kept unchanged.
-/
noncomputable def replaceRelatorSubset
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure ((R \ D) ∪ E))
    (hE : E ⊆ Subgroup.normalClosure R) :
    PresentedGroup R ≃* PresentedGroup ((R \ D) ∪ E) :=
  replaceRelators
    (S := (R \ D) ∪ E)
    (by
      intro r hr
      by_cases hd : r ∈ D
      · exact RelatorEquivalent.of_mem_normalClosure (hD r hd hr)
      · exact RelatorEquivalent.of_mem (R := (R \ D) ∪ E)
          (Or.inl ⟨hr, hd⟩))
    (by
      intro s hs
      rcases hs with hs | hs
      · exact RelatorEquivalent.of_mem (R := R) hs.1
      · exact RelatorEquivalent.of_mem_normalClosure (hE hs))

/-- Replacing a relator subset by relator-equivalent relators preserves relator equivalence. -/
noncomputable def replaceRelatorSubsetRelatorEquivalent
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → RelatorEquivalent ((R \ D) ∪ E) d 1)
    (hE : ∀ e ∈ E, RelatorEquivalent R e 1) :
    PresentedGroup R ≃* PresentedGroup ((R \ D) ∪ E) :=
  replaceRelatorSubset
    (R := R) (D := D) (E := E)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))
    (fun e he => RelatorEquivalent.mem_normalClosure_of_eq_one (hE e he))

/--
Replacing a subset of relators by another subset with the same normal closure is a Tietze
equivalence.
-/
def replaceRelatorSubsetTietzeEquiv
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → d ∈ Subgroup.normalClosure ((R \ D) ∪ E))
    (hE : E ⊆ Subgroup.normalClosure R) :
    TietzeEquiv R ((R \ D) ∪ E) :=
  replaceRelatorsTietzeEquiv
    (S := (R \ D) ∪ E)
    (by
      intro r hr
      by_cases hd : r ∈ D
      · exact RelatorEquivalent.of_mem_normalClosure (hD r hd hr)
      · exact RelatorEquivalent.of_mem (R := (R \ D) ∪ E)
          (Or.inl ⟨hr, hd⟩))
    (by
      intro s hs
      rcases hs with hs | hs
      · exact RelatorEquivalent.of_mem (R := R) hs.1
      · exact RelatorEquivalent.of_mem_normalClosure (hE hs))

/-- Replacing a relator subset by relator-equivalent relators gives a Tietze equivalence. -/
def replaceRelatorSubsetRelatorEquivalentTietzeEquiv
    {R D E : Set (FreeGroup X)}
    (hD :
      ∀ d ∈ D, d ∈ R → RelatorEquivalent ((R \ D) ∪ E) d 1)
    (hE : ∀ e ∈ E, RelatorEquivalent R e 1) :
    TietzeEquiv R ((R \ D) ∪ E) :=
  replaceRelatorSubsetTietzeEquiv
    (R := R) (D := D) (E := E)
    (fun d hd hR =>
      RelatorEquivalent.mem_normalClosure_of_eq_one (hD d hd hR))
    (fun e he => RelatorEquivalent.mem_normalClosure_of_eq_one (hE e he))

/-- Adding one redundant relator to a presented group does not change the presented group. -/
noncomputable def addRedundantRelator
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure R) :
    PresentedGroup (insert r R) ≃* PresentedGroup R :=
  ofNormalClosureEq (normalClosure_insert_eq_of_mem (R := R) hr)

/-- Adding one relator already in the normal closure is a Tietze equivalence. -/
def addRedundantRelatorTietzeEquiv
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure R) :
    TietzeEquiv (insert r R) R :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_insert_eq_of_mem (R := R) hr)

/-- Remove one redundant relator from a presented group without changing the presented group. -/
noncomputable def removeRedundantRelator
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure (R \ {r})) :
    PresentedGroup R ≃* PresentedGroup (R \ {r}) :=
  ofNormalClosureEq (normalClosure_diff_singleton_eq_of_mem (R := R) hr)

/--
Removing one relator whose normal closure is generated by the remaining relators is a Tietze
equivalence.
-/
def removeRedundantRelatorTietzeEquiv
    {R : Set (FreeGroup X)} {r : FreeGroup X}
    (hr : r ∈ Subgroup.normalClosure (R \ {r})) :
    TietzeEquiv R (R \ {r}) :=
  TietzeEquiv.ofNormalClosureEq
    (normalClosure_diff_singleton_eq_of_mem (R := R) hr)

/-- Rename the generators of a presented group. -/
noncomputable def renameGenerators
    (R : Set (FreeGroup X)) (e : X ≃ Y) :
    PresentedGroup R ≃*
      PresentedGroup (FreeGroup.freeGroupCongr e '' R) :=
  PresentedGroup.equivPresentedGroup R e

/-- Renaming generators along an equivalence gives a Tietze equivalence. -/
def renameGeneratorsTietzeEquiv
    (R : Set (FreeGroup X)) (e : X ≃ Y) :
    TietzeEquiv R (FreeGroup.freeGroupCongr e '' R) :=
  TietzeEquiv.ofMutualMapData
    (relatorQuotientMutualMapDataOfRelatorImagesMemNormalClosure
      (FreeGroup.freeGroupCongr e)
      R (FreeGroup.freeGroupCongr e '' R)
      (by
        intro r hr
        exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩)
      (by
        intro s hs
        rcases hs with ⟨r, hr, rfl⟩
        have hback :
            (FreeGroup.freeGroupCongr e).symm
                ((FreeGroup.freeGroupCongr e) r) = r :=
          (FreeGroup.freeGroupCongr e).left_inv r
        rw [hback]
        exact Subgroup.subset_normalClosure hr))

end Presented

end ReidemeisterSchreier.Discrete.Presentations
