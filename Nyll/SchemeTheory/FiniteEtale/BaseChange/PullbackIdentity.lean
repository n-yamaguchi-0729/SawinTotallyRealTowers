/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Identity coherence for the actual finite étale pullback

The identity comparison uses the first projection of the chosen pullback.
Its compatibility with a cone leg is proved by those actual projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

private def pullbackIdSchemeIso {A X : Scheme.{u}} (f : A ⟶ X) :
    Limits.pullback f (𝟙 X) ≅ A where
  hom := Limits.pullback.fst f (𝟙 X)
  inv := Limits.pullback.lift (𝟙 A) f
    ((Category.id_comp f).trans (Category.comp_id f).symm)
  hom_inv_id := by
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.condition, Category.comp_id, Category.id_comp]
  inv_hom_id := Limits.pullback.lift_fst _ _ _

/-- The canonical comparison between pullback by the identity and the
identity functor on finite étale covers. -/
def pullbackIdIso (X : Scheme.{u}) : pullback (𝟙 X) ≅ 𝟭 (FiniteEtale X) :=
  NatIso.ofComponents
    (fun A ↦
      MorphismProperty.Over.isoMk (pullbackIdSchemeIso A.hom)
        (Limits.pullback.condition.trans (Category.comp_id _)))
    (fun f ↦ by
      apply MorphismProperty.Over.Hom.ext
      exact Limits.pullback.lift_fst _ _ _)

/-- The identity comparison is the actual first pullback projection. -/
theorem pullbackIdIso_hom_app_left (X : Scheme.{u}) (A : FiniteEtale X) :
    ((pullbackIdIso X).hom.app A).left = Limits.pullback.fst A.hom (𝟙 X) :=
  rfl

/-- The forward composition comparison preserves the projection to the
original cover, with a specified composite morphism. -/
theorem pullbackComp_hom_app_left_fst_fst
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (m : X ⟶ Z) (hm : m = f ≫ g) (A : FiniteEtale Z) :
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) f g m hm).hom.app A).left ≫
      Limits.pullback.fst (Limits.pullback.snd A.hom g) f ≫
      Limits.pullback.fst A.hom g = Limits.pullback.fst A.hom m := by
  subst m
  exact MorphismProperty.Over.pullbackComp_left_fst_fst f g A

/-- Composing the canonical cone comparison with the identity comparison
does not change pullback along that cone leg. -/
theorem pullbackComp_id_coherence {X Y : Scheme.{u}} (p : X ⟶ Y) :
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) p (𝟙 Y) p (Category.comp_id p).symm ≪≫
      Functor.isoWhiskerRight (pullbackIdIso Y) (pullback p) ≪≫
      Functor.leftUnitor (pullback p) = Iso.refl (pullback p) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  let A₀ : Scheme := A.left
  let f : A₀ ⟶ Y := A.hom
  let A₁ : Scheme := Limits.pullback f (𝟙 Y)
  let f₁ : A₁ ⟶ Y := Limits.pullback.snd f (𝟙 Y)
  let D : Scheme := Limits.pullback f p
  let E : Scheme := Limits.pullback f₁ p
  let v : D ⟶ E := ((MorphismProperty.Over.pullbackComp
    (P := @IsFiniteEtale) (Q := ⊤) p (𝟙 Y) p (Category.comp_id p).symm).hom.app A).left
  let w : E ⟶ D := ((pullback p).map ((pullbackIdIso Y).hom.app A)).left
  let r : D ⟶ A₀ := Limits.pullback.fst f p
  let s : D ⟶ X := Limits.pullback.snd f p
  let r₁ : E ⟶ A₁ := Limits.pullback.fst f₁ p
  let r₀ : A₁ ⟶ A₀ := Limits.pullback.fst f (𝟙 Y)
  let s₁ : E ⟶ X := Limits.pullback.snd f₁ p
  have hv : v ≫ r₁ ≫ r₀ = r :=
    pullbackComp_hom_app_left_fst_fst p (𝟙 Y) p (Category.comp_id p).symm A
  have hw : w ≫ r = r₁ ≫ r₀ := Limits.pullback.lift_fst _ _ _
  have hvS : v ≫ s₁ = s := MorphismProperty.Over.w
    ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) p (𝟙 Y) p (Category.comp_id p).symm).hom.app A)
  have hwS : w ≫ s = s₁ := Limits.pullback.lift_snd _ _ _
  apply MorphismProperty.Over.Hom.ext
  change v ≫ (w ≫ 𝟙 D) = 𝟙 D
  rw [Category.comp_id]
  apply Limits.pullback.hom_ext
  · change (v ≫ w) ≫ r = 𝟙 D ≫ r
    exact (Category.assoc v w r).trans
      ((congrArg (fun t : E ⟶ A₀ ↦ v ≫ t) hw).trans
        (hv.trans (Category.id_comp r).symm))
  · change (v ≫ w) ≫ s = 𝟙 D ≫ s
    exact (Category.assoc v w s).trans
      ((congrArg (fun t : E ⟶ X ↦ v ≫ t) hwS).trans
        (hvS.trans (Category.id_comp s).symm))

end AlgebraicGeometry.FiniteEtale
