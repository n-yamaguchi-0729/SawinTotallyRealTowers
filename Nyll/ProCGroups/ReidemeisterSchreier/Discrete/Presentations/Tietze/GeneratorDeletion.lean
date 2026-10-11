/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.GeneratorAddition

/-!
# Reidemeister Schreier / Discrete / Presentations / Tietze / Generator Deletion

This module formalizes deletion of generators forced to be trivial.  It
defines the elimination homomorphism and relator transformations and packages
the induced equivalence of presented quotients.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

namespace Presented

variable {X Y : Type*}

section AdjoinGenerators

section DeleteTrivialGenerators

variable (X Y)

/--
The substitution map sends the generators in \(Y\) to \(1\), while keeping the old generators
\(X\). It is used by the Tietze move deleting generators with relators \(y = 1\).
-/
def trivializeGeneratorsHom : FreeGroup (Sum X Y) →* FreeGroup X :=
  eliminateAdjoinedGeneratorsHom (fun _ : Y => 1)

variable {X Y}

/-- The trivializing homomorphism fixes each retained generator \(x : X\). -/
@[simp]
theorem trivializeGeneratorsHom_inl (x : X) :
    trivializeGeneratorsHom X Y (FreeGroup.of (Sum.inl x)) =
      FreeGroup.of x := by
  simp only [trivializeGeneratorsHom, eliminateAdjoinedGeneratorsHom_inl]

/-- The trivializing homomorphism sends each deleted generator \(y : Y\) to \(1\). -/
@[simp]
theorem trivializeGeneratorsHom_inr (y : Y) :
    trivializeGeneratorsHom X Y (FreeGroup.of (Sum.inr y)) = 1 := by
  simp only [trivializeGeneratorsHom, eliminateAdjoinedGeneratorsHom_inr]

/--
Trivializing the deleted generators after including the retained generators is the identity on
the retained free group.
-/
theorem trivializeGeneratorsHom_comp_include :
    (trivializeGeneratorsHom X Y).comp (includeAdjoinedGenerators X Y) =
      MonoidHom.id (FreeGroup X) :=
  eliminateAdjoinedGeneratorsHom_comp_include (fun _ : Y => 1)

/-- Relators \(y = 1\) for a family of generators to be deleted. -/
def trivialGeneratorRelators :
    Set (FreeGroup (Sum X Y)) :=
  {q | ∃ y : Y, q = FreeGroup.of (Sum.inr y)}

/--
Adds the relators \(y = 1\) to a presentation over \(X \oplus Y\), trivializing the auxiliary
generators.
-/
def relatorsWithTrivialGenerators
    (R : Set (FreeGroup (Sum X Y))) :
    Set (FreeGroup (Sum X Y)) :=
  R ∪ trivialGeneratorRelators (X := X) (Y := Y)

/--
The relators after deleting the \(Y\)-generators are obtained by substituting them with \(1\).
-/
def relatorsAfterDeletingTrivialGenerators
    (R : Set (FreeGroup (Sum X Y))) :
    Set (FreeGroup X) :=
  trivializeGeneratorsHom X Y '' R

/-- Each trivial-generator relation \(y = 1\) belongs to the trivial-generator relator set. -/
theorem trivialGeneratorRelator_mem (y : Y) :
    FreeGroup.of (Sum.inr y) ∈
      trivialGeneratorRelators (X := X) (Y := Y) :=
  ⟨y, rfl⟩

/-- Each trivial-generator relation \(y = 1\) belongs to the relator set with trivial generators. -/
theorem trivialGeneratorRelator_mem_relatorsWithTrivialGenerators
    (R : Set (FreeGroup (Sum X Y))) (y : Y) :
    FreeGroup.of (Sum.inr y) ∈ relatorsWithTrivialGenerators R :=
  Or.inr (trivialGeneratorRelator_mem (X := X) (Y := Y) y)

/-- Every original relator belongs to the relator set with trivial generators. -/
theorem relator_mem_relatorsWithTrivialGenerators
    {R : Set (FreeGroup (Sum X Y))} {r : FreeGroup (Sum X Y)}
    (hr : r ∈ R) :
    r ∈ relatorsWithTrivialGenerators R :=
  Or.inl hr

/--
Including the result of trivializing deleted generators is congruent to the original word modulo
the trivial-generator relators.
-/
theorem include_trivializeGeneratorsHom_mod_trivialGeneratorRelators
    (z : FreeGroup (Sum X Y)) :
    includeAdjoinedGenerators X Y (trivializeGeneratorsHom X Y z) * z⁻¹ ∈
      Subgroup.normalClosure (trivialGeneratorRelators (X := X) (Y := Y)) := by
  let S : Set (FreeGroup (Sum X Y)) :=
    trivialGeneratorRelators (X := X) (Y := Y)
  let N : Subgroup (FreeGroup (Sum X Y)) := Subgroup.normalClosure S
  let F : FreeGroup (Sum X Y) →* FreeGroup (Sum X Y) :=
    (includeAdjoinedGenerators X Y).comp (trivializeGeneratorsHom X Y)
  have hhom : (QuotientGroup.mk' N).comp F = QuotientGroup.mk' N := by
    ext z
    cases z with
    | inl x =>
        simp only [includeAdjoinedGenerators, trivializeGeneratorsHom, MonoidHom.coe_comp,
            QuotientGroup.coe_mk',
  Function.comp_apply, eliminateAdjoinedGeneratorsHom_inl, FreeGroup.map.of,
      QuotientGroup.mk'_apply, N, F]
    | inr y =>
        simp only [MonoidHom.comp_apply, F, trivializeGeneratorsHom_inr,
          map_one]
        change ((1 : FreeGroup (Sum X Y)) : FreeGroup (Sum X Y) ⧸ N) =
          ((FreeGroup.of (Sum.inr y) : FreeGroup (Sum X Y)) :
            FreeGroup (Sum X Y) ⧸ N)
        apply (QuotientGroup.eq_iff_div_mem
          (N := N)
          (x := (1 : FreeGroup (Sum X Y)))
          (y := FreeGroup.of (Sum.inr y))).2
        have hrel :
            FreeGroup.of (Sum.inr y) ∈ N :=
          Subgroup.subset_normalClosure
            (trivialGeneratorRelator_mem (X := X) (Y := Y) y)
        simpa [N, div_eq_mul_inv] using N.inv_mem hrel
  have hz := congrArg (fun f : FreeGroup (Sum X Y) →*
      FreeGroup (Sum X Y) ⧸ N => f z) hhom
  change (includeAdjoinedGenerators X Y (trivializeGeneratorsHom X Y z) :
      FreeGroup (Sum X Y) ⧸ N) = z at hz
  exact (QuotientGroup.eq_iff_div_mem
    (N := N)
    (x := includeAdjoinedGenerators X Y (trivializeGeneratorsHom X Y z))
    (y := z)).1 hz

/--
Including the result of trivializing deleted generators is congruent to the original word modulo
the relators with trivial generators.
-/
theorem include_trivializeGeneratorsHom_mod_relatorsWithTrivialGenerators
    (R : Set (FreeGroup (Sum X Y))) (z : FreeGroup (Sum X Y)) :
    includeAdjoinedGenerators X Y (trivializeGeneratorsHom X Y z) * z⁻¹ ∈
      Subgroup.normalClosure (relatorsWithTrivialGenerators R) :=
  Subgroup.normalClosure_mono
    (fun _ hq => Or.inr hq)
    (include_trivializeGeneratorsHom_mod_trivialGeneratorRelators
      (X := X) (Y := Y) z)

/--
Deleting generators forced to be trivial gives mutual maps between the original presentation and
the reduced presentation.
-/
def deleteTrivialGeneratorsMutualMapData
    (R : Set (FreeGroup (Sum X Y))) :
    RelatorQuotientMutualMapData
      (relatorsWithTrivialGenerators R)
      (relatorsAfterDeletingTrivialGenerators R) where
  toHom := trivializeGeneratorsHom X Y
  invHom := includeAdjoinedGenerators X Y
  mapsRelators := by
    intro r hr
    rcases hr with hr | hr
    · exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩
    · rcases hr with ⟨y, rfl⟩
      simp only [trivializeGeneratorsHom_inr, one_mem]
  mapsTargetRelators := by
    intro s hs
    rcases hs with ⟨r, hr, rfl⟩
    let N : Subgroup (FreeGroup (Sum X Y)) :=
      Subgroup.normalClosure (relatorsWithTrivialGenerators R)
    have hmod :
        includeAdjoinedGenerators X Y (trivializeGeneratorsHom X Y r) *
            r⁻¹ ∈ N :=
      include_trivializeGeneratorsHom_mod_relatorsWithTrivialGenerators
        (X := X) (Y := Y) R r
    have hrN : r ∈ N :=
      Subgroup.subset_normalClosure
        (relator_mem_relatorsWithTrivialGenerators (R := R) hr)
    have hprod := Subgroup.mul_mem N hmod hrN
    convert hprod using 1
    group
  inv_toHom := by
    intro z
    exact include_trivializeGeneratorsHom_mod_relatorsWithTrivialGenerators
      (X := X) (Y := Y) R z
  to_invHom := by
    intro z
    have hcomp := congrArg (fun f : FreeGroup X →* FreeGroup X => f z)
      (trivializeGeneratorsHom_comp_include (X := X) (Y := Y))
    have hz :
        trivializeGeneratorsHom X Y (includeAdjoinedGenerators X Y z) = z := by
      simpa using hcomp
    simp only [hz, mul_inv_cancel, one_mem]

/-- Tietze equivalence deleting generators forced to be trivial by the relators \(y = 1\). -/
def deleteTrivialGeneratorsTietzeEquiv
    (R : Set (FreeGroup (Sum X Y))) :
    TietzeEquiv
      (relatorsWithTrivialGenerators R)
      (relatorsAfterDeletingTrivialGenerators R) :=
  TietzeEquiv.ofMutualMapData
    (deleteTrivialGeneratorsMutualMapData R)

/--
Tietze move deleting a family of generators that have relators y = 1. Every remaining relator is
pushed forward by substituting those deleted generators with 1.
-/
noncomputable def deleteTrivialGenerators
    (R : Set (FreeGroup (Sum X Y))) :
    PresentedGroup (relatorsWithTrivialGenerators R) ≃*
      PresentedGroup (relatorsAfterDeletingTrivialGenerators R) :=
  (deleteTrivialGeneratorsTietzeEquiv R).presentedEquiv

end DeleteTrivialGenerators

section DeleteGeneratorsAlongEquiv

variable {Z X Y : Type*}

namespace GeneratorPartition

/-- Generators kept after deleting the generators satisfying `delete`. -/
def Kept (delete : Z → Prop) : Type _ :=
  {z : Z // ¬ delete z}

/-- Generators deleted by a predicate `delete`. -/
def Deleted (delete : Z → Prop) : Type _ :=
  {z : Z // delete z}

/--
Split an arbitrary generator type into the generators kept and deleted by a decidable predicate.
-/
def equiv (delete : Z → Prop) [DecidablePred delete] :
    Z ≃ Sum (Kept delete) (Deleted delete) where
  toFun z :=
    if hz : delete z then
      Sum.inr ⟨z, hz⟩
    else
      Sum.inl ⟨z, hz⟩
  invFun z :=
    match z with
    | Sum.inl x => x.1
    | Sum.inr y => y.1
  left_inv z := by
    by_cases hz : delete z <;> simp only [hz, ↓reduceDIte]
  right_inv z := by
    cases z with
    | inl x =>
        simp only [Kept, Deleted, x.property, ↓reduceDIte]
        exact congrArg (fun z : Kept delete => (Sum.inl z : Sum (Kept delete) (Deleted delete)))
          (Subtype.ext rfl)
    | inr y =>
        simp only [Kept, Deleted, y.property, ↓reduceDIte]
        exact congrArg (fun z : Deleted delete => (Sum.inr z : Sum (Kept delete) (Deleted delete)))
          (Subtype.ext rfl)

/-- The partition equivalence sends a generator satisfying the deletion predicate to the
deleted summand. -/
@[simp]
theorem equiv_apply_of_delete
    (delete : Z → Prop) [DecidablePred delete]
    {z : Z} (hz : delete z) :
    equiv delete z = Sum.inr (⟨z, hz⟩ : Deleted delete) := by
  simp only [equiv, Equiv.coe_fn_mk, hz, ↓reduceDIte]
  congr

/-- The partition equivalence sends a retained generator to the kept summand. -/
@[simp]
theorem equiv_apply_of_not_delete
    (delete : Z → Prop) [DecidablePred delete]
    {z : Z} (hz : ¬ delete z) :
    equiv delete z = Sum.inl (⟨z, hz⟩ : Kept delete) := by
  simp only [equiv, Equiv.coe_fn_mk, hz, ↓reduceDIte]
  congr

/-- The inverse partition equivalence forgets the proof attached to a retained generator. -/
@[simp]
theorem equiv_symm_inl
    (delete : Z → Prop) [DecidablePred delete]
    (z : Kept delete) :
    (equiv delete).symm (Sum.inl z) = z.1 :=
  rfl

/-- The inverse partition equivalence forgets the proof attached to a deleted generator. -/
@[simp]
theorem equiv_symm_inr
    (delete : Z → Prop) [DecidablePred delete]
    (z : Deleted delete) :
    (equiv delete).symm (Sum.inr z) = z.1 :=
  rfl

end GeneratorPartition

/--
Pull back the defining relators \(y = \mathrm{word}(y)\) along an equivalence that splits an
arbitrary generator type into kept and deleted generators.
-/
def definedGeneratorRelatorsAlongEquiv
    (e : Z ≃ Sum X Y) (word : Y → FreeGroup X) :
    Set (FreeGroup Z) :=
  (FreeGroup.freeGroupCongr e).symm ''
    definedGeneratorRelators (X := X) (Y := Y) word

/--
Add defining relators to an arbitrary presentation whose generator type is identified with \(X
\oplus Y\).
-/
def relatorsWithDefinedGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    Set (FreeGroup Z) :=
  R ∪ definedGeneratorRelatorsAlongEquiv e word

/--
Relators after renaming by \(e\) and substituting every deleted generator \(y : Y\) by
\(\mathrm{word}(y)\).
-/
def relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    Set (FreeGroup X) :=
  relatorsAfterSubstitutingDefinedGenerators
    (FreeGroup.freeGroupCongr e '' R) word

/--
Renaming generators carries the pulled-back defining-generator relators to the
defining-generator relators after the split.
-/
theorem freeGroupCongr_image_definedGeneratorRelatorsAlongEquiv
    (e : Z ≃ Sum X Y) (word : Y → FreeGroup X) :
    FreeGroup.freeGroupCongr e ''
        definedGeneratorRelatorsAlongEquiv e word =
      definedGeneratorRelators (X := X) (Y := Y) word := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨p, hp, hpz⟩
    have hpmap :
        FreeGroup.map (fun z : Z => e z)
            (FreeGroup.map (fun z : Sum X Y => e.symm z) p) = p := by
      simpa [FreeGroup.freeGroupCongr] using
        (FreeGroup.freeGroupCongr e).right_inv p
    simpa [FreeGroup.freeGroupCongr, ← hpz, hpmap] using hp
  · intro hq
    exact ⟨(FreeGroup.freeGroupCongr e).symm q, ⟨q, hq, rfl⟩,
      (FreeGroup.freeGroupCongr e).right_inv q⟩

/--
Renaming generators carries the pulled-back relators with defined generators to the
corresponding split relator set.
-/
theorem freeGroupCongr_image_relatorsWithDefinedGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    FreeGroup.freeGroupCongr e ''
        relatorsWithDefinedGeneratorsAlongEquiv R e word =
      relatorsWithDefinedGenerators
        (FreeGroup.freeGroupCongr e '' R) word := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact Or.inl ⟨z, hz, rfl⟩
    · rcases hz with ⟨p, hp, hpz⟩
      exact Or.inr (by
        have hpmap :
            FreeGroup.map (fun z : Z => e z)
                (FreeGroup.map (fun z : Sum X Y => e.symm z) p) = p := by
          simpa [FreeGroup.freeGroupCongr] using
            (FreeGroup.freeGroupCongr e).right_inv p
        simpa [FreeGroup.freeGroupCongr, ← hpz, hpmap] using hp)
  · intro hq
    rcases hq with hq | hq
    · rcases hq with ⟨z, hz, hzq⟩
      exact ⟨z, Or.inl hz, hzq⟩
    · exact ⟨(FreeGroup.freeGroupCongr e).symm q,
        Or.inr ⟨q, hq, rfl⟩,
        (FreeGroup.freeGroupCongr e).right_inv q⟩

/--
Tietze move eliminating an arbitrary family of generators after splitting the generator type by
an equivalence \(Z \simeq X \oplus Y\).
-/
def substituteDefinedGeneratorsAlongEquivTietzeEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    TietzeEquiv
      (relatorsWithDefinedGeneratorsAlongEquiv R e word)
      (relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv R e word) :=
  (renameGeneratorsTietzeEquiv
      (relatorsWithDefinedGeneratorsAlongEquiv R e word) e).trans
    ((TietzeEquiv.ofNormalClosureEq
      (R := FreeGroup.freeGroupCongr e ''
        relatorsWithDefinedGeneratorsAlongEquiv R e word)
      (S := relatorsWithDefinedGenerators
        (FreeGroup.freeGroupCongr e '' R) word)
      (by
        rw [freeGroupCongr_image_relatorsWithDefinedGeneratorsAlongEquiv])).trans
      (substituteDefinedGeneratorsTietzeEquiv
        (FreeGroup.freeGroupCongr e '' R) word))

/-- Defines `substituteDefinedGeneratorsAlongEquiv`. -/
noncomputable def substituteDefinedGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y)
    (word : Y → FreeGroup X) :
    PresentedGroup (relatorsWithDefinedGeneratorsAlongEquiv R e word) ≃*
      PresentedGroup
        (relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv R e word) :=
  (substituteDefinedGeneratorsAlongEquivTietzeEquiv R e word).presentedEquiv

/--
Add defining relations for all generators satisfying the deletion predicate; the kept generator
type is the subtype of generators not satisfying that predicate.
-/
def definedGeneratorRelatorsOfPredicate
    (delete : Z → Prop) [DecidablePred delete]
    (word :
      GeneratorPartition.Deleted delete →
        FreeGroup (GeneratorPartition.Kept delete)) :
    Set (FreeGroup Z) :=
  definedGeneratorRelatorsAlongEquiv
    (GeneratorPartition.equiv delete) word

/--
The relator set obtained by adding defining relators for all generators satisfying the
predicate.
-/
def relatorsWithDefinedGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete]
    (word :
      GeneratorPartition.Deleted delete →
        FreeGroup (GeneratorPartition.Kept delete)) :
    Set (FreeGroup Z) :=
  relatorsWithDefinedGeneratorsAlongEquiv R
    (GeneratorPartition.equiv delete) word

/--
Relators obtained after substituting every generator satisfying the predicate by its defining
word.
-/
def relatorsAfterSubstitutingDefinedGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete]
    (word :
      GeneratorPartition.Deleted delete →
        FreeGroup (GeneratorPartition.Kept delete)) :
    Set (FreeGroup (GeneratorPartition.Kept delete)) :=
  relatorsAfterSubstitutingDefinedGeneratorsAlongEquiv R
    (GeneratorPartition.equiv delete) word

/--
Tietze equivalence substituting the generators satisfying the predicate by their defining words.
-/
def substituteDefinedGeneratorsOfPredicateTietzeEquiv
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete]
    (word :
      GeneratorPartition.Deleted delete →
        FreeGroup (GeneratorPartition.Kept delete)) :
    TietzeEquiv
      (relatorsWithDefinedGeneratorsOfPredicate R delete word)
      (relatorsAfterSubstitutingDefinedGeneratorsOfPredicate R delete word) :=
  substituteDefinedGeneratorsAlongEquivTietzeEquiv R
    (GeneratorPartition.equiv delete) word

/-- Defines `substituteDefinedGeneratorsOfPredicate`. -/
noncomputable def substituteDefinedGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete]
    (word :
      GeneratorPartition.Deleted delete →
        FreeGroup (GeneratorPartition.Kept delete)) :
    PresentedGroup (relatorsWithDefinedGeneratorsOfPredicate R delete word) ≃*
      PresentedGroup
        (relatorsAfterSubstitutingDefinedGeneratorsOfPredicate R delete word) :=
  (substituteDefinedGeneratorsOfPredicateTietzeEquiv R delete word).presentedEquiv

/--
Pull back the trivial-generator relators \(y = 1\) along an equivalence that splits an arbitrary
generator type into kept and deleted generators.
-/
def trivialGeneratorRelatorsAlongEquiv
    (e : Z ≃ Sum X Y) :
    Set (FreeGroup Z) :=
  (FreeGroup.freeGroupCongr e).symm ''
    trivialGeneratorRelators (X := X) (Y := Y)

/--
Add trivial-generator relators to an arbitrary presentation whose generator type is identified
with \(X \oplus Y\).
-/
def relatorsWithTrivialGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    Set (FreeGroup Z) :=
  R ∪ trivialGeneratorRelatorsAlongEquiv e

/-- Relators after renaming by \(e\) and deleting every generator in \(Y\). -/
def relatorsAfterDeletingTrivialGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    Set (FreeGroup X) :=
  relatorsAfterDeletingTrivialGenerators (FreeGroup.freeGroupCongr e '' R)

/--
Renaming generators carries the pulled-back trivial-generator relators to the trivial-generator
relators after the split.
-/
theorem freeGroupCongr_image_trivialGeneratorRelatorsAlongEquiv
    (e : Z ≃ Sum X Y) :
    FreeGroup.freeGroupCongr e ''
        trivialGeneratorRelatorsAlongEquiv (X := X) (Y := Y) e =
      trivialGeneratorRelators (X := X) (Y := Y) := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨p, hp, hpz⟩
    have hpmap :
        FreeGroup.map (fun z : Z => e z)
            (FreeGroup.map (fun z : Sum X Y => e.symm z) p) = p := by
      simpa [FreeGroup.freeGroupCongr] using
        (FreeGroup.freeGroupCongr e).right_inv p
    simpa [FreeGroup.freeGroupCongr, ← hpz, hpmap] using hp
  · intro hq
    exact ⟨(FreeGroup.freeGroupCongr e).symm q, ⟨q, hq, rfl⟩,
      (FreeGroup.freeGroupCongr e).right_inv q⟩

/--
Renaming generators carries the pulled-back relators with trivial generators to the
corresponding split relator set.
-/
theorem freeGroupCongr_image_relatorsWithTrivialGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    FreeGroup.freeGroupCongr e ''
        relatorsWithTrivialGeneratorsAlongEquiv R e =
      relatorsWithTrivialGenerators (FreeGroup.freeGroupCongr e '' R) := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact Or.inl ⟨z, hz, rfl⟩
    · rcases hz with ⟨p, hp, hpz⟩
      exact Or.inr (by
        have hpmap :
            FreeGroup.map (fun z : Z => e z)
                (FreeGroup.map (fun z : Sum X Y => e.symm z) p) = p := by
          simpa [FreeGroup.freeGroupCongr] using
            (FreeGroup.freeGroupCongr e).right_inv p
        simpa [FreeGroup.freeGroupCongr, ← hpz, hpmap] using hp)
  · intro hq
    rcases hq with hq | hq
    · rcases hq with ⟨z, hz, hzq⟩
      exact ⟨z, Or.inl hz, hzq⟩
    · exact ⟨(FreeGroup.freeGroupCongr e).symm q,
        Or.inr ⟨q, hq, rfl⟩,
        (FreeGroup.freeGroupCongr e).right_inv q⟩

/--
Tietze move deleting an arbitrary family of generators after splitting the generator type by an
equivalence \(Z \simeq X \oplus Y\).
-/
def deleteTrivialGeneratorsAlongEquivTietzeEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    TietzeEquiv
      (relatorsWithTrivialGeneratorsAlongEquiv R e)
      (relatorsAfterDeletingTrivialGeneratorsAlongEquiv R e) :=
  (renameGeneratorsTietzeEquiv
      (relatorsWithTrivialGeneratorsAlongEquiv R e) e).trans
    ((TietzeEquiv.ofNormalClosureEq
      (R := FreeGroup.freeGroupCongr e ''
        relatorsWithTrivialGeneratorsAlongEquiv R e)
      (S := relatorsWithTrivialGenerators
        (FreeGroup.freeGroupCongr e '' R))
      (by
        rw [freeGroupCongr_image_relatorsWithTrivialGeneratorsAlongEquiv])).trans
      (deleteTrivialGeneratorsTietzeEquiv
        (FreeGroup.freeGroupCongr e '' R)))

/-- Defines `deleteTrivialGeneratorsAlongEquiv`. -/
noncomputable def deleteTrivialGeneratorsAlongEquiv
    (R : Set (FreeGroup Z)) (e : Z ≃ Sum X Y) :
    PresentedGroup (relatorsWithTrivialGeneratorsAlongEquiv R e) ≃*
      PresentedGroup
        (relatorsAfterDeletingTrivialGeneratorsAlongEquiv R e) :=
  (deleteTrivialGeneratorsAlongEquivTietzeEquiv R e).presentedEquiv

/-- Trivial-generator relators for the generators satisfying the deletion predicate. -/
def trivialGeneratorRelatorsOfPredicate
    (delete : Z → Prop) [DecidablePred delete] :
    Set (FreeGroup Z) :=
  trivialGeneratorRelatorsAlongEquiv
    (X := GeneratorPartition.Kept delete)
    (Y := GeneratorPartition.Deleted delete)
    (GeneratorPartition.equiv delete)

/--
The relator set obtained by adding trivial-generator relators for all generators satisfying the
predicate.
-/
def relatorsWithTrivialGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete] :
    Set (FreeGroup Z) :=
  relatorsWithTrivialGeneratorsAlongEquiv R
    (X := GeneratorPartition.Kept delete)
    (Y := GeneratorPartition.Deleted delete)
    (GeneratorPartition.equiv delete)

/--
Relators obtained after deleting every generator satisfying the predicate by substituting it
with \(1\).
-/
def relatorsAfterDeletingTrivialGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete] :
    Set (FreeGroup (GeneratorPartition.Kept delete)) :=
  relatorsAfterDeletingTrivialGeneratorsAlongEquiv R
    (X := GeneratorPartition.Kept delete)
    (Y := GeneratorPartition.Deleted delete)
    (GeneratorPartition.equiv delete)

/-- Tietze equivalence deleting the generators satisfying the chosen predicate. -/
def deleteTrivialGeneratorsOfPredicateTietzeEquiv
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete] :
    TietzeEquiv
      (relatorsWithTrivialGeneratorsOfPredicate R delete)
      (relatorsAfterDeletingTrivialGeneratorsOfPredicate R delete) :=
  deleteTrivialGeneratorsAlongEquivTietzeEquiv R
    (X := GeneratorPartition.Kept delete)
    (Y := GeneratorPartition.Deleted delete)
    (GeneratorPartition.equiv delete)

/-- Defines `deleteTrivialGeneratorsOfPredicate`. -/
noncomputable def deleteTrivialGeneratorsOfPredicate
    (R : Set (FreeGroup Z)) (delete : Z → Prop) [DecidablePred delete] :
    PresentedGroup (relatorsWithTrivialGeneratorsOfPredicate R delete) ≃*
      PresentedGroup
        (relatorsAfterDeletingTrivialGeneratorsOfPredicate R delete) :=
  (deleteTrivialGeneratorsOfPredicateTietzeEquiv R delete).presentedEquiv

end DeleteGeneratorsAlongEquiv

end AdjoinGenerators

end Presented

end ReidemeisterSchreier.Discrete.Presentations
