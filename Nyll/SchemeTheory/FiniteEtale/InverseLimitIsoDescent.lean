/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsomorphism
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition

/-!
# Actual isomorphism descent along inverse limits

An isomorphism between the pullbacks of two finite-etale models descends to
an actual isomorphism at a later stage. The comparison with the given map
is retained under the literal native pullback-composition isomorphism.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryIsoDescent (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongIsoDescent
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongIsoDescent
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private theorem pullback_map_left_fst {S T : Scheme.{u}} (f : S ⟶ T)
    {A B : FiniteEtale T} (a : A ⟶ B) :
    ((FiniteEtale.pullback f).map a).left ≫ Limits.pullback.fst B.hom f =
      Limits.pullback.fst A.hom f ≫ a.left :=
  Limits.pullback.lift_fst _ _ _

/-- The native comparisons for two consecutive inverse-system transitions
cohere with the comparison for their composite. -/
theorem inverseLimitPullbackComparison_inv_comp
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j k : I} (hji : j ⟶ i) (hkj : k ⟶ j) (A : FiniteEtale (D.obj i)) :
    let E : FiniteEtale.pullback (D.map (hkj ≫ hji)) ≅
        FiniteEtale.pullback (D.map hji) ⋙ FiniteEtale.pullback (D.map hkj) :=
      MorphismProperty.Over.pullbackComp
        (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
        (D.map hkj) (D.map hji) (D.map (hkj ≫ hji)) (D.map_comp hkj hji)
    (FiniteEtale.pullback (c.π.app k)).map (E.inv.app A) ≫
        (inverseLimitPullbackComparison D c (hkj ≫ hji)).inv.app A =
      (inverseLimitPullbackComparison D c hkj).inv.app
          ((FiniteEtale.pullback (D.map hji)).obj A) ≫
        (inverseLimitPullbackComparison D c hji).inv.app A := by
  intro E
  let f : A.left ⟶ D.obj i := A.hom
  let qj : Limits.pullback f (D.map hji) ⟶ D.obj j := Limits.pullback.snd f (D.map hji)
  let qk : Limits.pullback qj (D.map hkj) ⟶ D.obj k := Limits.pullback.snd qj (D.map hkj)
  let qt : Limits.pullback f (D.map (hkj ≫ hji)) ⟶ D.obj k :=
    Limits.pullback.snd f (D.map (hkj ≫ hji))
  let a : Limits.pullback qk (c.π.app k) ⟶ Limits.pullback qt (c.π.app k) :=
    ((FiniteEtale.pullback (c.π.app k)).map (E.inv.app A)).left
  let b : Limits.pullback qt (c.π.app k) ⟶ Limits.pullback f (c.π.app i) :=
    ((inverseLimitPullbackComparison D c (hkj ≫ hji)).inv.app A).left
  let d : Limits.pullback qk (c.π.app k) ⟶ Limits.pullback qj (c.π.app j) :=
    ((inverseLimitPullbackComparison D c hkj).inv.app
      ((FiniteEtale.pullback (D.map hji)).obj A)).left
  let e : Limits.pullback qj (c.π.app j) ⟶ Limits.pullback f (c.π.app i) :=
    ((inverseLimitPullbackComparison D c hji).inv.app A).left
  let v : Limits.pullback qj (D.map hkj) ⟶ Limits.pullback f (D.map (hkj ≫ hji)) :=
    (E.inv.app A).left
  have ha : a ≫ Limits.pullback.fst qt (c.π.app k) = Limits.pullback.fst qk (c.π.app k) ≫ v :=
    pullback_map_left_fst (c.π.app k) (E.inv.app A)
  have hb : b ≫ Limits.pullback.fst f (c.π.app i) =
      Limits.pullback.fst qt (c.π.app k) ≫ Limits.pullback.fst f (D.map (hkj ≫ hji)) :=
    pullbackComp_inv_app_left_fst (c.π.app k) (D.map (hkj ≫ hji))
      (c.π.app i) (c.w (hkj ≫ hji)).symm A
  have hd : d ≫ Limits.pullback.fst qj (c.π.app j) =
      Limits.pullback.fst qk (c.π.app k) ≫ Limits.pullback.fst qj (D.map hkj) :=
    pullbackComp_inv_app_left_fst (c.π.app k) (D.map hkj)
      (c.π.app j) (c.w hkj).symm ((FiniteEtale.pullback (D.map hji)).obj A)
  have he : e ≫ Limits.pullback.fst f (c.π.app i) =
      Limits.pullback.fst qj (c.π.app j) ≫ Limits.pullback.fst f (D.map hji) :=
    pullbackComp_inv_app_left_fst (c.π.app j) (D.map hji)
      (c.π.app i) (c.w hji).symm A
  have hv : v ≫ Limits.pullback.fst f (D.map (hkj ≫ hji)) =
      Limits.pullback.fst qj (D.map hkj) ≫ Limits.pullback.fst f (D.map hji) :=
    pullbackComp_inv_app_left_fst (D.map hkj) (D.map hji)
      (D.map (hkj ≫ hji)) (D.map_comp hkj hji) A
  have has : a ≫ Limits.pullback.snd qt (c.π.app k) = Limits.pullback.snd qk (c.π.app k) :=
    MorphismProperty.Over.w ((FiniteEtale.pullback (c.π.app k)).map (E.inv.app A))
  have hbs : b ≫ Limits.pullback.snd f (c.π.app i) = Limits.pullback.snd qt (c.π.app k) :=
    MorphismProperty.Over.w ((inverseLimitPullbackComparison D c (hkj ≫ hji)).inv.app A)
  have hds : d ≫ Limits.pullback.snd qj (c.π.app j) = Limits.pullback.snd qk (c.π.app k) :=
    MorphismProperty.Over.w ((inverseLimitPullbackComparison D c hkj).inv.app
      ((FiniteEtale.pullback (D.map hji)).obj A))
  have hes : e ≫ Limits.pullback.snd f (c.π.app i) = Limits.pullback.snd qj (c.π.app j) :=
    MorphismProperty.Over.w ((inverseLimitPullbackComparison D c hji).inv.app A)
  apply MorphismProperty.Over.Hom.ext
  change a ≫ b = d ≫ e
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc, hv,
      Category.assoc, he, ← Category.assoc d, hd, Category.assoc]
  · rw [Category.assoc, hbs, has, Category.assoc, hes, hds]

end AlgebraicGeometry.FiniteEtale
