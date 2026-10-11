/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Native finite-etale morphisms descend along inverse limits

Translate the actual scheme Hom descent through pullback symmetry and retain
the canonical pullback-composition comparison. The output is a morphism in
the native finite-etale category with its categorical recovery equation.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryLimitHom (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
  instCategory X

local instance finiteEtaleHasPullbacksAlongLimitHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongLimitHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private abbrev rawToStage {L T S Y : Scheme.{u}}
    (p : L ⟶ S) (q : T ⟶ S) (r : L ⟶ T) (w : r ≫ q = p) (f : Y ⟶ S) :
    Limits.pullback p f ⟶ Limits.pullback q f :=
  ((Over.pullback f).map (Over.homMk r w : Over.mk p ⟶ Over.mk q)).left

private def toStage {L T S Y : Scheme.{u}}
    (p : L ⟶ S) (q : T ⟶ S) (r : L ⟶ T) (w : r ≫ q = p) (f : Y ⟶ S) :
    Limits.pullback f p ⟶ Limits.pullback f q :=
  Limits.pullback.lift (Limits.pullback.fst f p) (Limits.pullback.snd f p ≫ r)
    (by rw [Category.assoc, w]; exact Limits.pullback.condition)

private theorem toStage_eq_symmetry {L T S Y : Scheme.{u}}
    (p : L ⟶ S) (q : T ⟶ S) (r : L ⟶ T) (w : r ≫ q = p) (f : Y ⟶ S) :
    toStage p q r w f = (pullbackSymmetry p f).inv ≫
      rawToStage p q r w f ≫ (pullbackSymmetry q f).hom := by
  apply Limits.pullback.hom_ext
  · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst f q = _
    rw [Limits.pullback.lift_fst, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_fst]
    change Limits.pullback.fst f p = (pullbackSymmetry p f).inv ≫
      (Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd q f)
    rw [Limits.pullback.lift_snd]
    change Limits.pullback.fst f p = (pullbackSymmetry p f).inv ≫ Limits.pullback.snd p f
    exact (pullbackSymmetry_inv_comp_snd p f).symm
  · change Limits.pullback.lift _ _ _ ≫ Limits.pullback.snd f q = _
    rw [Limits.pullback.lift_snd, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_snd]
    change Limits.pullback.snd f p ≫ r = (pullbackSymmetry p f).inv ≫
      (Limits.pullback.lift _ _ _ ≫ Limits.pullback.fst q f)
    rw [Limits.pullback.lift_fst]
    change Limits.pullback.snd f p ≫ r =
      (pullbackSymmetry p f).inv ≫ (Limits.pullback.fst p f ≫ r)
    rw [← Category.assoc, pullbackSymmetry_inv_comp_fst]

private theorem pullbackComp_hom_toStage {L T S : Scheme.{u}}
    (p : L ⟶ S) (q : T ⟶ S) (r : L ⟶ T) (w : r ≫ q = p) (A : FiniteEtale S) :
    ((MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      r q p w.symm).hom.app A).left ≫
        Limits.pullback.fst (Limits.pullback.snd A.hom q) r = toStage p q r w A.hom := by
  let Y : Scheme.{u} := A.left
  let f : Y ⟶ S := A.hom
  let e := (MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) r q p w.symm).app A
  let eh : Limits.pullback f p ⟶
      Limits.pullback (Limits.pullback.snd f q) r := e.hom.left
  let ei : Limits.pullback (Limits.pullback.snd f q) r ⟶
      Limits.pullback f p := e.inv.left
  have hei : eh ≫ ei = 𝟙 (Limits.pullback f p) := by
    exact congrArg (fun v ↦ v.left) e.hom_inv_id
  have hfst : ei ≫ Limits.pullback.fst f p =
      Limits.pullback.fst (Limits.pullback.snd f q) r ≫
        Limits.pullback.fst f q :=
    pullbackComp_inv_app_left_fst r q p w.symm A
  have hsnd : eh ≫ Limits.pullback.snd (Limits.pullback.snd f q) r =
      Limits.pullback.snd f p := MorphismProperty.Over.w e.hom
  change eh ≫ Limits.pullback.fst (Limits.pullback.snd f q) r = _
  apply Limits.pullback.hom_ext
  · change (eh ≫ Limits.pullback.fst (Limits.pullback.snd f q) r) ≫
        Limits.pullback.fst f q = Limits.pullback.lift _ _ _ ≫ _
    rw [Limits.pullback.lift_fst, Category.assoc, ← hfst, ← Category.assoc,
      hei, Category.id_comp]
  · change (eh ≫ Limits.pullback.fst (Limits.pullback.snd f q) r) ≫
        Limits.pullback.snd f q = Limits.pullback.lift _ _ _ ≫ _
    rw [Limits.pullback.lift_snd, Category.assoc, Limits.pullback.condition,
      ← Category.assoc, hsnd]

/-- The canonical comparison from a model pulled directly to the limit to
the same model pulled through a later stage. -/
def inverseLimitPullbackComparison
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    {i j : I} (h : j ⟶ i) :
    FiniteEtale.pullback (c.π.app i) ≅
      FiniteEtale.pullback (D.map h) ⋙ FiniteEtale.pullback (c.π.app j) :=
  MorphismProperty.Over.pullbackComp
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
    (c.π.app j) (D.map h) (c.π.app i) (c.w h).symm

/-- An arbitrary morphism between pulled-back finite-etale models descends
to a later original stage. Recovery uses the native pullback-composition
comparison, not a separate assumed compatibility. -/
theorem exists_inverse_limit_stage_hom
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (A B : FiniteEtale (D.obj i))
    (a : (FiniteEtale.pullback (c.π.app i)).obj A ⟶
      (FiniteEtale.pullback (c.π.app i)).obj B) :
    ∃ (j : I) (hji : j ⟶ i)
      (b : (FiniteEtale.pullback (D.map hji)).obj A ⟶
        (FiniteEtale.pullback (D.map hji)).obj B),
      (inverseLimitPullbackComparison D c hji).hom.app A ≫
          (FiniteEtale.pullback (c.π.app j)).map b =
        a ≫ (inverseLimitPullbackComparison D c hji).hom.app B := by
  let YA : Scheme.{u} := A.left
  let YB : Scheme.{u} := B.left
  let f : YA ⟶ D.obj i := A.hom
  let g : YB ⟶ D.obj i := B.hom
  have : IsFiniteEtale f := A.prop
  have : IsFiniteEtale g := B.prop
  let p : c.pt ⟶ D.obj i := c.π.app i
  let a₀ : Limits.pullback f p ⟶ Limits.pullback g p := a.left
  have ha₀ : a₀ ≫ Limits.pullback.snd g p = Limits.pullback.snd f p :=
    MorphismProperty.Over.w a
  let ar : Limits.pullback p f ⟶ Limits.pullback p g :=
    (pullbackSymmetry p f).hom ≫ a₀ ≫ (pullbackSymmetry p g).inv
  have har : ar ≫ Limits.pullback.fst p g = Limits.pullback.fst p f := by
    dsimp only [ar]
    simp only [Category.assoc, pullbackSymmetry_inv_comp_fst, ha₀,
      pullbackSymmetry_hom_comp_snd]
  obtain ⟨j, hji, br, hbr, hrec⟩ :=
    AffineTransitionHom.exists_hom_later_stage D c hc i f g ar har
  let q := D.map hji
  let r := c.π.app j
  let b₀ : Limits.pullback f q ⟶ Limits.pullback g q :=
    (pullbackSymmetry q f).inv ≫ br ≫ (pullbackSymmetry q g).hom
  have hbr' : br ≫ Limits.pullback.fst q g = Limits.pullback.fst q f := hbr
  have hb₀ : b₀ ≫ Limits.pullback.snd g q = Limits.pullback.snd f q := by
    dsimp only [b₀]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, hbr',
      pullbackSymmetry_inv_comp_fst]
  let b : (FiniteEtale.pullback q).obj A ⟶ (FiniteEtale.pullback q).obj B :=
    MorphismProperty.Over.homMk b₀ hb₀
  have hrec' : toStage p q r (c.w hji) f ≫ b₀ =
      a₀ ≫ toStage p q r (c.w hji) g := by
    change rawToStage p q r (c.w hji) f ≫ br =
      ar ≫ rawToStage p q r (c.w hji) g at hrec
    have H := congrArg (fun v : Limits.pullback p f ⟶ Limits.pullback q g ↦
      (pullbackSymmetry p f).inv ≫ v ≫ (pullbackSymmetry q g).hom) hrec
    simpa only [toStage_eq_symmetry, b₀, ar, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] using H
  refine ⟨j, hji, b, ?_⟩
  let e := inverseLimitPullbackComparison D c hji
  let eA : Limits.pullback f p ⟶ Limits.pullback (Limits.pullback.snd f q) r :=
    (e.hom.app A).left
  let eB : Limits.pullback g p ⟶ Limits.pullback (Limits.pullback.snd g q) r :=
    (e.hom.app B).left
  let β : Limits.pullback (Limits.pullback.snd f q) r ⟶
      Limits.pullback (Limits.pullback.snd g q) r := ((FiniteEtale.pullback r).map b).left
  have hβfst : β ≫ Limits.pullback.fst (Limits.pullback.snd g q) r =
      Limits.pullback.fst (Limits.pullback.snd f q) r ≫ b₀ :=
    Limits.pullback.lift_fst _ _ _
  have hβsnd : β ≫ Limits.pullback.snd (Limits.pullback.snd g q) r =
      Limits.pullback.snd (Limits.pullback.snd f q) r :=
    Limits.pullback.lift_snd _ _ _
  have heA : eA ≫
      Limits.pullback.fst (Limits.pullback.snd f q) r =
        toStage p q r (c.w hji) f :=
    pullbackComp_hom_toStage p q r (c.w hji) A
  have heB : eB ≫
      Limits.pullback.fst (Limits.pullback.snd g q) r =
        toStage p q r (c.w hji) g :=
    pullbackComp_hom_toStage p q r (c.w hji) B
  have heAsnd : eA ≫ Limits.pullback.snd (Limits.pullback.snd f q) r =
      Limits.pullback.snd f p := MorphismProperty.Over.w (e.hom.app A)
  have heBsnd : eB ≫ Limits.pullback.snd (Limits.pullback.snd g q) r =
      Limits.pullback.snd g p := MorphismProperty.Over.w (e.hom.app B)
  apply MorphismProperty.Over.Hom.ext
  change eA ≫ β = a₀ ≫ eB
  apply Limits.pullback.hom_ext
  · rw [Category.assoc, hβfst, ← Category.assoc]
    rw [heA, Category.assoc, heB]
    exact hrec'
  · rw [Category.assoc, hβsnd, heAsnd, Category.assoc, heBsnd, ha₀]

end AlgebraicGeometry.FiniteEtale
