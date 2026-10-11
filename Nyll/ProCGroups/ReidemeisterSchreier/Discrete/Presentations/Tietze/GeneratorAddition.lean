/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Tietze.RelatorReplacement

/-!
# Reidemeister Schreier / Discrete / Presentations / Tietze / Generator Addition

This module formalizes adjoining generators with defining words.  It builds
the inclusion and elimination homomorphisms, transforms the relators, and
packages the resulting presented-group equivalence.
-/

universe u v w

namespace ReidemeisterSchreier.Discrete.Presentations

namespace Presented

variable {X Y : Type*}

section AdjoinGenerators

variable (X Y)

/-- Include the old free group into the free group with a family of new generators. -/
def includeAdjoinedGenerators : FreeGroup X →* FreeGroup (Sum X Y) :=
  FreeGroup.map Sum.inl

variable {X Y}

/-- The elimination homomorphism sends every new generator \(y : Y\) to \(\mathrm{word}(y)\). -/
def eliminateAdjoinedGeneratorsHom (word : Y → FreeGroup X) :
    FreeGroup (Sum X Y) →* FreeGroup X :=
  FreeGroup.lift (fun z =>
    match z with
    | Sum.inl x => FreeGroup.of x
    | Sum.inr y => word y)

/-- The elimination homomorphism fixes each original generator \(x : X\). -/
@[simp]
theorem eliminateAdjoinedGeneratorsHom_inl
    (word : Y → FreeGroup X) (x : X) :
    eliminateAdjoinedGeneratorsHom word (FreeGroup.of (Sum.inl x)) =
      FreeGroup.of x := by
  simp only [eliminateAdjoinedGeneratorsHom, FreeGroup.lift_apply_of]

/-- The elimination homomorphism sends each adjoined generator \(y : Y\) to its defining word. -/
@[simp]
theorem eliminateAdjoinedGeneratorsHom_inr
    (word : Y → FreeGroup X) (y : Y) :
    eliminateAdjoinedGeneratorsHom word (FreeGroup.of (Sum.inr y)) =
      word y := by
  simp only [eliminateAdjoinedGeneratorsHom, FreeGroup.lift_apply_of]

/--
Eliminating the adjoined generators after including the original free group is the identity on
the original free group.
-/
theorem eliminateAdjoinedGeneratorsHom_comp_include
    (word : Y → FreeGroup X) :
    (eliminateAdjoinedGeneratorsHom word).comp (includeAdjoinedGenerators X Y) =
      MonoidHom.id (FreeGroup X) := by
  ext x
  simp only [includeAdjoinedGenerators, MonoidHom.coe_comp, Function.comp_apply, FreeGroup.map.of,
  eliminateAdjoinedGeneratorsHom_inl, MonoidHom.id_apply]

/-- Relators after adjoining generators \(y : Y\) and relations \(y = \mathrm{word}(y)\). -/
def adjoinGeneratorsRelators
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
    Set (FreeGroup (Sum X Y)) :=
  (includeAdjoinedGenerators X Y) '' R ∪
    {q | ∃ y : Y,
      q = FreeGroup.of (Sum.inr y) *
        (includeAdjoinedGenerators X Y (word y))⁻¹}

/--
Each defining relation \(y = \mathrm{word}(y)\) for an adjoined generator belongs to the
adjoined-generator relator set.
-/
theorem adjoinGenerators_relation_mem
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X) (y : Y) :
    FreeGroup.of (Sum.inr y) *
        (includeAdjoinedGenerators X Y (word y))⁻¹ ∈
      adjoinGeneratorsRelators R word := by
  exact Or.inr ⟨y, rfl⟩

/--
Including the result of eliminating adjoined generators is congruent to the original word modulo
the adjoined-generator relators.
-/
theorem include_eliminateAdjoinedGeneratorsHom_mod_relators
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X)
    (z : FreeGroup (Sum X Y)) :
    includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z) *
        z⁻¹ ∈
      Subgroup.normalClosure (adjoinGeneratorsRelators R word) := by
  let S : Set (FreeGroup (Sum X Y)) := adjoinGeneratorsRelators R word
  let N : Subgroup (FreeGroup (Sum X Y)) := Subgroup.normalClosure S
  let F : FreeGroup (Sum X Y) →* FreeGroup (Sum X Y) :=
    (includeAdjoinedGenerators X Y).comp (eliminateAdjoinedGeneratorsHom word)
  have hhom : (QuotientGroup.mk' N).comp F = QuotientGroup.mk' N := by
    ext z
    cases z with
    | inl x =>
        simp only [includeAdjoinedGenerators, MonoidHom.coe_comp, QuotientGroup.coe_mk',
            Function.comp_apply,
  eliminateAdjoinedGeneratorsHom_inl, FreeGroup.map.of, QuotientGroup.mk'_apply, N, F]
    | inr y =>
        simp only [MonoidHom.comp_apply, F, eliminateAdjoinedGeneratorsHom,
          FreeGroup.lift_apply_of]
        change ((includeAdjoinedGenerators X Y (word y) : FreeGroup (Sum X Y)) :
            FreeGroup (Sum X Y) ⧸ N) =
          ((FreeGroup.of (Sum.inr y) : FreeGroup (Sum X Y)) :
            FreeGroup (Sum X Y) ⧸ N)
        apply (QuotientGroup.eq_iff_div_mem
          (N := N)
          (x := includeAdjoinedGenerators X Y (word y))
          (y := FreeGroup.of (Sum.inr y))).2
        have hrel :
            FreeGroup.of (Sum.inr y) *
                (includeAdjoinedGenerators X Y (word y))⁻¹ ∈ N :=
          Subgroup.subset_normalClosure
            (adjoinGenerators_relation_mem R word y)
        have hinv :
            (FreeGroup.of (Sum.inr y) *
                (includeAdjoinedGenerators X Y (word y))⁻¹)⁻¹ ∈ N :=
          N.inv_mem hrel
        simpa [N, div_eq_mul_inv, mul_assoc] using hinv
  have hz := congrArg (fun f : FreeGroup (Sum X Y) →*
      FreeGroup (Sum X Y) ⧸ N => f z) hhom
  change (includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z) :
      FreeGroup (Sum X Y) ⧸ N) = z at hz
  exact (QuotientGroup.eq_iff_div_mem
    (N := N)
    (x := includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z))
    (y := z)).1 hz

/--
Adding generators with defining relations gives mutual maps between the original relator
quotient and the enlarged one.
-/
def adjoinGeneratorsMutualMapData
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
    RelatorQuotientMutualMapData R (adjoinGeneratorsRelators R word) where
  toHom := includeAdjoinedGenerators X Y
  invHom := eliminateAdjoinedGeneratorsHom word
  mapsRelators := by
    intro r hr
    exact Subgroup.subset_normalClosure (Or.inl ⟨r, hr, rfl⟩)
  mapsTargetRelators := by
    intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨r, hr, rfl⟩
      have hcomp := congrArg (fun f : FreeGroup X →* FreeGroup X => f r)
        (eliminateAdjoinedGeneratorsHom_comp_include word)
      have hrw :
          eliminateAdjoinedGeneratorsHom word (includeAdjoinedGenerators X Y r) = r := by
        simpa using hcomp
      simpa [hrw] using (Subgroup.subset_normalClosure hr :
        r ∈ Subgroup.normalClosure R)
    · rcases hs with ⟨y, rfl⟩
      have hw :
          eliminateAdjoinedGeneratorsHom word
              (includeAdjoinedGenerators X Y (word y)) = word y := by
        have hcomp := congrArg (fun f : FreeGroup X →* FreeGroup X => f (word y))
          (eliminateAdjoinedGeneratorsHom_comp_include word)
        simpa using hcomp
      simp only [map_mul, map_inv, eliminateAdjoinedGeneratorsHom_inr]
      change word y *
          (eliminateAdjoinedGeneratorsHom word
            (includeAdjoinedGenerators X Y (word y)))⁻¹ ∈
        Subgroup.normalClosure R
      simp only [hw, mul_inv_cancel, one_mem]
  inv_toHom := by
    intro x
    have hcomp := congrArg (fun f : FreeGroup X →* FreeGroup X => f x)
      (eliminateAdjoinedGeneratorsHom_comp_include word)
    have hx :
        eliminateAdjoinedGeneratorsHom word (includeAdjoinedGenerators X Y x) = x := by
      simpa using hcomp
    simp only [hx, mul_inv_cancel, one_mem]
  to_invHom := by
    intro z
    exact include_eliminateAdjoinedGeneratorsHom_mod_relators R word z

/--
The Tietze equivalence obtained by adjoining generators \(y : Y\) with defining relations \(y =
\mathrm{word}(y)\).
-/
def adjoinGeneratorsTietzeEquiv
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
    TietzeEquiv R (adjoinGeneratorsRelators R word) :=
  TietzeEquiv.ofMutualMapData (adjoinGeneratorsMutualMapData R word)

/-- Tietze move: adding a family of generators \(y : Y\) with relations \(y = \mathrm{word}(y)\). -/
noncomputable def adjoinGenerators
    (R : Set (FreeGroup X)) (word : Y → FreeGroup X) :
    PresentedGroup R ≃*
      PresentedGroup (adjoinGeneratorsRelators R word) :=
  (adjoinGeneratorsTietzeEquiv R word).presentedEquiv

section SubstituteDefinedGenerators

/--
Relations \(y = \mathrm{word}(y)\) for generators that will be eliminated from an arbitrary
presentation over \(X \oplus Y\).
-/
def definedGeneratorRelators
    (word : Y → FreeGroup X) :
    Set (FreeGroup (Sum X Y)) :=
  {q | ∃ y : Y,
    q = FreeGroup.of (Sum.inr y) *
      (includeAdjoinedGenerators X Y (word y))⁻¹}

/--
Add defining relations \(y = \mathrm{word}(y)\) to an arbitrary presentation over \(X \oplus
Y\). Unlike \(\mathrm{adjoinGeneratorsRelators}\), the old relators may already involve the
\(Y\)-generators.
-/
def relatorsWithDefinedGenerators
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) :
    Set (FreeGroup (Sum X Y)) :=
  R ∪ definedGeneratorRelators word

/-- Relators after substituting every generator \(y : Y\) by \(\mathrm{word}(y)\). -/
def relatorsAfterSubstitutingDefinedGenerators
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) :
    Set (FreeGroup X) :=
  eliminateAdjoinedGeneratorsHom word '' R

/--
Each defining relation \(y = \mathrm{word}(y)\) belongs to the defining-generator relator set.
-/
theorem definedGeneratorRelator_mem
    (word : Y → FreeGroup X) (y : Y) :
    FreeGroup.of (Sum.inr y) *
        (includeAdjoinedGenerators X Y (word y))⁻¹ ∈
      definedGeneratorRelators word :=
  ⟨y, rfl⟩

/--
Each defining relation \(y = \mathrm{word}(y)\) belongs to the relator set with defined
generators.
-/
theorem definedGeneratorRelator_mem_relatorsWithDefinedGenerators
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) (y : Y) :
    FreeGroup.of (Sum.inr y) *
        (includeAdjoinedGenerators X Y (word y))⁻¹ ∈
      relatorsWithDefinedGenerators R word :=
  Or.inr (definedGeneratorRelator_mem word y)

/-- Every original relator belongs to the relator set with defined generators. -/
theorem relator_mem_relatorsWithDefinedGenerators
    {R : Set (FreeGroup (Sum X Y))} {word : Y → FreeGroup X}
    {r : FreeGroup (Sum X Y)} (hr : r ∈ R) :
    r ∈ relatorsWithDefinedGenerators R word :=
  Or.inl hr

/--
Including the result of eliminating adjoined generators is congruent to the original word modulo
the defining-generator relators.
-/
theorem include_eliminateAdjoinedGeneratorsHom_mod_definedGeneratorRelators
    (word : Y → FreeGroup X) (z : FreeGroup (Sum X Y)) :
    includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z) *
        z⁻¹ ∈
      Subgroup.normalClosure (definedGeneratorRelators word) := by
  let S : Set (FreeGroup (Sum X Y)) := definedGeneratorRelators word
  let N : Subgroup (FreeGroup (Sum X Y)) := Subgroup.normalClosure S
  let F : FreeGroup (Sum X Y) →* FreeGroup (Sum X Y) :=
    (includeAdjoinedGenerators X Y).comp (eliminateAdjoinedGeneratorsHom word)
  have hhom : (QuotientGroup.mk' N).comp F = QuotientGroup.mk' N := by
    ext z
    cases z with
    | inl x =>
        simp only [includeAdjoinedGenerators, MonoidHom.coe_comp, QuotientGroup.coe_mk',
            Function.comp_apply,
  eliminateAdjoinedGeneratorsHom_inl, FreeGroup.map.of, QuotientGroup.mk'_apply, N, F]
    | inr y =>
        simp only [MonoidHom.comp_apply, F, eliminateAdjoinedGeneratorsHom,
          FreeGroup.lift_apply_of]
        change ((includeAdjoinedGenerators X Y (word y) : FreeGroup (Sum X Y)) :
            FreeGroup (Sum X Y) ⧸ N) =
          ((FreeGroup.of (Sum.inr y) : FreeGroup (Sum X Y)) :
            FreeGroup (Sum X Y) ⧸ N)
        apply (QuotientGroup.eq_iff_div_mem
          (N := N)
          (x := includeAdjoinedGenerators X Y (word y))
          (y := FreeGroup.of (Sum.inr y))).2
        have hrel :
            FreeGroup.of (Sum.inr y) *
                (includeAdjoinedGenerators X Y (word y))⁻¹ ∈ N :=
          Subgroup.subset_normalClosure
            (definedGeneratorRelator_mem word y)
        have hinv :
            (FreeGroup.of (Sum.inr y) *
                (includeAdjoinedGenerators X Y (word y))⁻¹)⁻¹ ∈ N :=
          N.inv_mem hrel
        simpa [N, div_eq_mul_inv, mul_assoc] using hinv
  have hz := congrArg (fun f : FreeGroup (Sum X Y) →*
      FreeGroup (Sum X Y) ⧸ N => f z) hhom
  change (includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z) :
      FreeGroup (Sum X Y) ⧸ N) = z at hz
  exact (QuotientGroup.eq_iff_div_mem
    (N := N)
    (x := includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z))
    (y := z)).1 hz

/--
Including the result of eliminating defined generators is congruent to the original word modulo
the relators with defined generators.
-/
theorem include_eliminateAdjoinedGeneratorsHom_mod_relatorsWithDefinedGenerators
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X)
    (z : FreeGroup (Sum X Y)) :
    includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word z) *
        z⁻¹ ∈
      Subgroup.normalClosure (relatorsWithDefinedGenerators R word) :=
  Subgroup.normalClosure_mono
    (fun _ hq => Or.inr hq)
    (include_eliminateAdjoinedGeneratorsHom_mod_definedGeneratorRelators
      (X := X) (Y := Y) word z)

/--
Substituting each defined generator by its defining word gives mutual maps for the presentation
with those generators eliminated.
-/
def substituteDefinedGeneratorsMutualMapData
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) :
    RelatorQuotientMutualMapData
      (relatorsWithDefinedGenerators R word)
      (relatorsAfterSubstitutingDefinedGenerators R word) where
  toHom := eliminateAdjoinedGeneratorsHom word
  invHom := includeAdjoinedGenerators X Y
  mapsRelators := by
    intro r hr
    rcases hr with hr | hr
    · exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩
    · rcases hr with ⟨y, rfl⟩
      have hw :
          eliminateAdjoinedGeneratorsHom word
              (includeAdjoinedGenerators X Y (word y)) = word y := by
        have hcomp := congrArg (fun f : FreeGroup X →* FreeGroup X => f (word y))
          (eliminateAdjoinedGeneratorsHom_comp_include word)
        simpa using hcomp
      simp only [map_mul, map_inv, eliminateAdjoinedGeneratorsHom_inr]
      change word y *
          (eliminateAdjoinedGeneratorsHom word
            (includeAdjoinedGenerators X Y (word y)))⁻¹ ∈
        Subgroup.normalClosure (relatorsAfterSubstitutingDefinedGenerators R word)
      simp only [hw, mul_inv_cancel, one_mem]
  mapsTargetRelators := by
    intro s hs
    rcases hs with ⟨r, hr, rfl⟩
    let N : Subgroup (FreeGroup (Sum X Y)) :=
      Subgroup.normalClosure (relatorsWithDefinedGenerators R word)
    have hmod :
        includeAdjoinedGenerators X Y (eliminateAdjoinedGeneratorsHom word r) *
            r⁻¹ ∈ N :=
      include_eliminateAdjoinedGeneratorsHom_mod_relatorsWithDefinedGenerators
        (X := X) (Y := Y) R word r
    have hrN : r ∈ N :=
      Subgroup.subset_normalClosure
        (relator_mem_relatorsWithDefinedGenerators (R := R) (word := word) hr)
    have hprod := Subgroup.mul_mem N hmod hrN
    convert hprod using 1
    group
  inv_toHom := by
    intro z
    exact include_eliminateAdjoinedGeneratorsHom_mod_relatorsWithDefinedGenerators
      (X := X) (Y := Y) R word z
  to_invHom := by
    intro z
    have hcomp := congrArg (fun f : FreeGroup X →* FreeGroup X => f z)
      (eliminateAdjoinedGeneratorsHom_comp_include word)
    have hz :
        eliminateAdjoinedGeneratorsHom word (includeAdjoinedGenerators X Y z) = z := by
      simpa using hcomp
    simp only [hz, mul_inv_cancel, one_mem]

/-- The Tietze equivalence obtained by substituting each defined generator by its defining word. -/
def substituteDefinedGeneratorsTietzeEquiv
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) :
    TietzeEquiv
      (relatorsWithDefinedGenerators R word)
      (relatorsAfterSubstitutingDefinedGenerators R word) :=
  TietzeEquiv.ofMutualMapData
    (substituteDefinedGeneratorsMutualMapData R word)

/--
Tietze move eliminating generators \(y : Y\) using relations \(y = \mathrm{word}(y)\), while
substituting \(\mathrm{word}(y)\) into all remaining relators.
-/
noncomputable def substituteDefinedGenerators
    (R : Set (FreeGroup (Sum X Y))) (word : Y → FreeGroup X) :
    PresentedGroup (relatorsWithDefinedGenerators R word) ≃*
      PresentedGroup (relatorsAfterSubstitutingDefinedGenerators R word) :=
  (substituteDefinedGeneratorsTietzeEquiv R word).presentedEquiv

end SubstituteDefinedGenerators

end AdjoinGenerators

end Presented

end ReidemeisterSchreier.Discrete.Presentations
