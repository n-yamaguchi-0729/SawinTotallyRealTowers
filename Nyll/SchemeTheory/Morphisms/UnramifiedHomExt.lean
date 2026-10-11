/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Equalizer

/-!
# Unramified morphisms are determined on a dense source

The equalizer of two relative morphisms into an unramified scheme is an open
subscheme. If the target is also separated, the equalizer is closed. Thus
agreement after a dominant morphism forces the equalizer to be the entire
source, without a reducedness assumption.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- The relative equalizer of two maps into an unramified scheme is open. -/
instance isOpenImmersion_equalizer_ι_left {S : Scheme.{u}} {X Y : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] (f g : X ⟶ Y) :
    IsOpenImmersion (equalizer.ι f g).left := by
  have hdiag :
      (prod.lift (𝟙 Y) (𝟙 Y)).left ≫ (Over.prodLeftIsoPullback Y Y).hom =
        pullback.diagonal Y.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_fst,
        ← Over.comp_left, prod.lift_fst, Over.id_left, pullback.diagonal_fst]
    · simp only [Category.assoc, Over.prodLeftIsoPullback_hom_snd,
        ← Over.comp_left, prod.lift_snd, Over.id_left, pullback.diagonal_snd]
  apply MorphismProperty.of_isPullback
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
    ((isPullback_equalizer_prod f g).map (Over.forget S)).flip
  change IsOpenImmersion (prod.lift (𝟙 Y) (𝟙 Y)).left
  rw [← MorphismProperty.cancel_right_of_respectsIso
    (P := (@IsOpenImmersion : MorphismProperty Scheme.{u}))
      _ (Over.prodLeftIsoPullback Y Y).hom, hdiag]
  infer_instance

/-- Relative maps into a separated unramified scheme are determined after
a dominant map, even when the source is nonreduced. -/
lemma Over.hom_ext_of_isDominant_of_unramified
    {S : Scheme.{u}} {X Y Z : Over S}
    [FormallyUnramified Y.hom] [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (i : Z ⟶ X) [IsDominant i.left]
    (h : i ≫ f = i ≫ g) : f = g := by
  let l : Z ⟶ equalizer f g := equalizer.lift i h
  have hl : l.left ≫ (equalizer.ι f g).left = i.left :=
    congrArg (fun a : Z ⟶ X ↦ a.left) (equalizer.lift_ι i h)
  let : IsDominant (l.left ≫ (equalizer.ι f g).left) := hl.symm ▸ inferInstance
  let : IsDominant (equalizer.ι f g).left :=
    IsDominant.of_comp l.left (equalizer.ι f g).left
  let : Surjective (equalizer.ι f g).left :=
    surjective_of_isDominant_of_isClosed_range _
      (Scheme.Hom.isClosedEmbedding (equalizer.ι f g).left).isClosed_range
  let : IsIso (equalizer.ι f g).left :=
    (isIso_iff_isOpenImmersion_and_surjective (equalizer.ι f g).left).mpr
      ⟨inferInstance, inferInstance⟩
  apply CategoryTheory.Over.OverMorphism.ext
  apply (cancel_epi (equalizer.ι f g).left).mp
  exact congrArg (fun a : equalizer f g ⟶ Y ↦ a.left) (equalizer.condition f g)

end AlgebraicGeometry
