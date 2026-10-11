/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Projection formulas for canonical finite étale pullback composition

These scheme-level formulas are shared by geometric descent and pointed
fundamental-group comparison.  They retain the actual chosen pullbacks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance finiteEtaleOverCategoryCoherence (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
  instCategory X

local instance finiteEtaleHasPullbacksAlongCoherence
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongCoherence
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {W X Y Z : Scheme.{u}}

/-- The inverse comparison between a composite and an iterated pullback
preserves the projection to the original covering scheme. -/
theorem pullbackComp_inv_app_left_fst
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (A : FiniteEtale Z) :
    ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g m hm).inv.app A).left ≫
        Limits.pullback.fst A.hom m =
      Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫
        Limits.pullback.fst A.hom g := by
  subst m
  change ((pullbackLeftPullbackSndIso A.hom g f).hom ≫
      (Limits.pullback.congrHom (rfl : A.hom = A.hom)
        (rfl : f ≫ g = f ≫ g)).inv) ≫
      Limits.pullback.fst A.hom (f ≫ g) = _
  rw [Category.assoc, Limits.pullback.congrHom_inv,
    Limits.pullback.lift_fst, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_fst A.hom g f

/-- The inverse comparison preserves the projection to the new base. -/
theorem pullbackComp_inv_app_left_snd
    (f : X ⟶ Y) (g : Y ⟶ Z) (m : X ⟶ Z) (hm : m = f ≫ g)
    (A : FiniteEtale Z) :
    ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g m hm).inv.app A).left ≫
        Limits.pullback.snd A.hom m =
      Limits.pullback.snd (Limits.pullback.snd A.hom g) f := by
  subst m
  change ((pullbackLeftPullbackSndIso A.hom g f).hom ≫
      (Limits.pullback.congrHom (rfl : A.hom = A.hom)
        (rfl : f ≫ g = f ≫ g)).inv) ≫
      Limits.pullback.snd A.hom (f ≫ g) = _
  rw [Category.assoc, Limits.pullback.congrHom_inv,
    Limits.pullback.lift_snd, Category.comp_id]
  exact pullbackLeftPullbackSndIso_hom_snd A.hom g f

end AlgebraicGeometry.FiniteEtale
