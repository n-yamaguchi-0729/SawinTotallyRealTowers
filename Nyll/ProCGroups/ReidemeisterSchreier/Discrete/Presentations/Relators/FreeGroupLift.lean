/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Basic

/-!
# Free-group lifts modulo relators

This module relates reduced words and FreeGroup.mk, then proves that lifts
whose generator images agree modulo a relator normal closure agree on every
free-group word.
-/

namespace ReidemeisterSchreier.Discrete.Presentations

variable {G H : Type*} [Group G] [Group H]

section NormalClosure

variable {R S : Set G} {r a b : G}

section FreeGroupLift

variable {X : Type*}

/--
A free-group element is relator-equivalent to the word built from a list when its word
representation reduces to that list.
-/
theorem freeGroup_relatorEquivalent_of_toWord_eq_reduce
    [DecidableEq X]
    {R : Set (FreeGroup X)} {u : FreeGroup X} {w : List (X × Bool)}
    (h : u.toWord = FreeGroup.reduce w) :
    RelatorEquivalent R u (FreeGroup.mk w) := by
  apply RelatorEquivalent.of_eq
  rw [← FreeGroup.toWord_inj]
  simp only [h, FreeGroup.toWord_mk]

/--
A free-group word is relator-equivalent to the word built from a list when their reduced words
agree.
-/
theorem freeGroup_relatorEquivalent_mk_of_reduce_eq
    [DecidableEq X]
    {R : Set (FreeGroup X)} {u : FreeGroup X} {w : List (X × Bool)}
    (h : FreeGroup.reduce w = u.toWord) :
    RelatorEquivalent R (FreeGroup.mk w) u :=
  (freeGroup_relatorEquivalent_of_toWord_eq_reduce
    (R := R) (u := u) (w := w) h.symm).symm

/-- Expand each signed source letter to the reduced word of its image, reversing and inverting
negative letters. -/
def freeGroupSubstitutionWord {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) :
    List (X × Bool) → List (Y × Bool)
  | [] => []
  | (x, true) :: xs => (f x).toWord ++ freeGroupSubstitutionWord f xs
  | (x, false) :: xs => FreeGroup.invRev (f x).toWord ++ freeGroupSubstitutionWord f xs

/-- Substitution sends the empty word to the empty word. -/
@[simp]
theorem freeGroupSubstitutionWord_nil {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) :
    freeGroupSubstitutionWord f [] = [] :=
  rfl

/-- Substitution of a positive letter prepends the reduced word of its image. -/
@[simp]
theorem freeGroupSubstitutionWord_cons_true {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) (x : X) (xs : List (X × Bool)) :
    freeGroupSubstitutionWord f ((x, true) :: xs) =
      (f x).toWord ++ freeGroupSubstitutionWord f xs :=
  rfl

/-- Substitution of a negative letter prepends the inverse-reversal of its image word. -/
@[simp]
theorem freeGroupSubstitutionWord_cons_false {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) (x : X) (xs : List (X × Bool)) :
    freeGroupSubstitutionWord f ((x, false) :: xs) =
      FreeGroup.invRev (f x).toWord ++ freeGroupSubstitutionWord f xs :=
  rfl

/-- Substitution preserves concatenation of signed words. -/
theorem freeGroupSubstitutionWord_append {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) (xs ys : List (X × Bool)) :
    freeGroupSubstitutionWord f (xs ++ ys) =
      freeGroupSubstitutionWord f xs ++ freeGroupSubstitutionWord f ys := by
  induction xs with
  | nil => simp
  | cons xb xs ih =>
      rcases xb with ⟨x, b⟩
      cases b
      · simp only [List.cons_append, freeGroupSubstitutionWord_cons_false, ih, List.append_assoc]
      · simp only [List.cons_append, freeGroupSubstitutionWord_cons_true, ih, List.append_assoc]

/-- Evaluating a substitution word agrees with applying the free-group lift. -/
theorem freeGroup_mk_substitutionWord {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) (xs : List (X × Bool)) :
    FreeGroup.mk (freeGroupSubstitutionWord f xs) =
      FreeGroup.lift f (FreeGroup.mk xs) := by
  induction xs with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons xb xs ih =>
      rcases xb with ⟨x, b⟩
      cases b
      · rw [freeGroupSubstitutionWord_cons_false, ← FreeGroup.mul_mk,
          ← FreeGroup.inv_mk, FreeGroup.mk_toWord, ih]
        simp only [FreeGroup.lift_mk, List.map_cons, Bool.cond_false, List.prod_cons]
      · rw [freeGroupSubstitutionWord_cons_true, ← FreeGroup.mul_mk,
          FreeGroup.mk_toWord, ih]
        simp only [FreeGroup.lift_mk, List.map_cons, Bool.cond_true, List.prod_cons]

/-- The lifted generator maps to the corresponding word in the free-group presentation. -/
theorem freeGroup_toWord_lift_mk {Y : Type*} [DecidableEq Y]
    (f : X → FreeGroup Y) (xs : List (X × Bool)) :
    (FreeGroup.lift f (FreeGroup.mk xs)).toWord =
      FreeGroup.reduce (freeGroupSubstitutionWord f xs) := by
  rw [← freeGroup_mk_substitutionWord (f := f) (xs := xs)]
  simp only [FreeGroup.toWord_mk]

/-- The free-group lift of a reduced substitution word agrees with the corresponding generator. -/
theorem freeGroup_lift_mk_eq_mk_of_substitutionWord_reduce_eq
    {Y : Type*} [DecidableEq Y]
    {f : X → FreeGroup Y} {xs : List (X × Bool)}
    {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce (freeGroupSubstitutionWord f xs) =
        FreeGroup.reduce ys) :
    FreeGroup.lift f (FreeGroup.mk xs) = FreeGroup.mk ys := by
  rw [← FreeGroup.toWord_inj]
  rw [freeGroup_toWord_lift_mk, FreeGroup.toWord_mk, h]

/--
A lifted generator word is relator-equivalent to the corresponding word when the substitution
word has the stated reduction.
-/
theorem freeGroup_relatorEquivalent_lift_mk_of_substitutionWord_reduce_eq
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup Y)}
    {f : X → FreeGroup Y} {xs : List (X × Bool)}
    {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce (freeGroupSubstitutionWord f xs) =
        FreeGroup.reduce ys) :
    RelatorEquivalent R (FreeGroup.lift f (FreeGroup.mk xs))
      (FreeGroup.mk ys) :=
  RelatorEquivalent.of_eq
    (freeGroup_lift_mk_eq_mk_of_substitutionWord_reduce_eq h)

/--
A lifted generator word is relator-equivalent to the identity when its substitution word reduces
to the empty word.
-/
theorem freeGroup_relatorEquivalent_lift_mk_one_of_substitutionWord_reduce_eq
    {Y : Type*} [DecidableEq Y]
    {R : Set (FreeGroup Y)}
    {f : X → FreeGroup Y} {xs : List (X × Bool)}
    {ys : List (Y × Bool)}
    (h :
      FreeGroup.reduce (freeGroupSubstitutionWord f xs) =
        FreeGroup.reduce ys)
    (hy : RelatorEquivalent R (FreeGroup.mk ys) 1) :
    RelatorEquivalent R (FreeGroup.lift f (FreeGroup.mk xs)) 1 :=
  (freeGroup_relatorEquivalent_lift_mk_of_substitutionWord_reduce_eq
    (R := R) h).trans hy

/--
A free-group lift preserves relator equivalence when the generator images are
relator-equivalent.
-/
theorem freeGroup_lift_relatorEquivalent_of_generator_relatorEquivalent
    {R : Set G} {f g : X → G}
    (h : ∀ x : X, RelatorEquivalent R (f x) (g x))
    (w : FreeGroup X) :
    RelatorEquivalent R (FreeGroup.lift f w) (FreeGroup.lift g w) := by
  let N : Subgroup G := Subgroup.normalClosure R
  let F : FreeGroup X →* G ⧸ N :=
    (QuotientGroup.mk' N).comp (FreeGroup.lift f)
  let K : FreeGroup X →* G ⧸ N :=
    (QuotientGroup.mk' N).comp (FreeGroup.lift g)
  have hhom : F = K := by
    ext x
    dsimp [F, K]
    simp only [FreeGroup.lift_apply_of]
    rw [← relatorEquivalent_iff_eq_in_presentedQuotient]
    exact h x
  have hw := congrArg (fun φ : FreeGroup X →* G ⧸ N => φ w) hhom
  change ((FreeGroup.lift f w : G) : G ⧸ N) =
    ((FreeGroup.lift g w : G) : G ⧸ N) at hw
  exact relatorEquivalent_iff_eq_in_presentedQuotient.2 hw

/--
A free-group lift sends the word to a relator-equivalent trivial word when the generator images
are relator-equivalent to one.
-/
theorem freeGroup_lift_relatorEquivalent_one_of_generator_relatorEquivalent
    {R : Set G} {f : X → G}
    (h : ∀ x : X, RelatorEquivalent R (f x) 1)
    (w : FreeGroup X) :
    RelatorEquivalent R (FreeGroup.lift f w) 1 := by
  let trivialLift : FreeGroup X →* G :=
    FreeGroup.lift (fun _ : X => (1 : G))
  have htrivial : trivialLift w = 1 := by
    have hhom : trivialLift = 1 := by
      ext x
      simp only [FreeGroup.lift_apply_of, MonoidHom.one_apply, trivialLift]
    exact congrArg (fun φ : FreeGroup X →* G => φ w) hhom
  simpa [trivialLift, htrivial] using
    freeGroup_lift_relatorEquivalent_of_generator_relatorEquivalent
      (R := R) (f := f) (g := fun _ : X => (1 : G)) h w

/-- A free-group lift preserves relator equivalence when the generator images are equal. -/
theorem freeGroup_lift_relatorEquivalent_of_generator_eq
    {R : Set G} {f g : X → G}
    (h : ∀ x : X, f x = g x)
    (w : FreeGroup X) :
    RelatorEquivalent R (FreeGroup.lift f w) (FreeGroup.lift g w) :=
  freeGroup_lift_relatorEquivalent_of_generator_relatorEquivalent
    (R := R) (f := f) (g := g)
    (fun x => RelatorEquivalent.of_eq (h x)) w

end FreeGroupLift

end NormalClosure

end ReidemeisterSchreier.Discrete.Presentations
