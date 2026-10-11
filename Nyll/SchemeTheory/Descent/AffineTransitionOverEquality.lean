/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Eventual equations of actual relative scheme models

The diagonal and triple objects used in scheme gluing are finite etale over
compact overlaps, rather than over the whole ambient stage. Their structural
maps to that stage are quasi-compact and locally of finite type. The existing
raw affine-transition equality theorem supplies eventual equality of their
native `Over.pullback` maps.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

/-- Morphisms of quasi-compact models into locally finite-type models that
agree after limit pullback agree after a later original transition. -/
theorem exists_over_map_eq_later_stage
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) {A B : Over (D.obj i)} [QuasiCompact A.hom] [LocallyOfFiniteType B.hom]
    (a b : A ⟶ B)
    (hab : (Over.pullback (c.π.app i)).map a =
      (Over.pullback (c.π.app i)).map b) :
    ∃ (j : I) (hji : j ⟶ i),
      (Over.pullback (D.map hji)).map a =
        (Over.pullback (D.map hji)).map b := by
  let YA : Scheme.{u} := A.left
  let YB : Scheme.{u} := B.left
  let f : YA ⟶ D.obj i := A.hom
  let g : YB ⟶ D.obj i := B.hom
  let F : Over i ⥤ Over (D.obj i) := Over.post D
  let s : Cone F := (Over.conePost D i).obj c
  let p : c.pt ⟶ D.obj i := c.π.app i
  let a₀ : YA ⟶ YB := a.left
  let b₀ : YA ⟶ YB := b.left
  have ha₀ : a₀ ≫ g = f := Over.w a
  have hb₀ : b₀ ≫ g = f := Over.w b
  have hraw : Limits.pullback.snd p f ≫ a₀ =
      Limits.pullback.snd p f ≫ b₀ := by
    have H := congrArg (fun v ↦ v.left) hab
    have haproj : ((Over.pullback p).map a).left ≫ Limits.pullback.fst g p =
        Limits.pullback.fst f p ≫ a₀ := Limits.pullback.lift_fst _ _ _
    have hbproj : ((Over.pullback p).map b).left ≫ Limits.pullback.fst g p =
        Limits.pullback.fst f p ≫ b₀ := Limits.pullback.lift_fst _ _ _
    have Hfst : Limits.pullback.fst f p ≫ a₀ = Limits.pullback.fst f p ≫ b₀ :=
      haproj.symm.trans ((congrArg
        (fun v : Limits.pullback f p ⟶ Limits.pullback g p ↦
          v ≫ Limits.pullback.fst g p) H).trans hbproj)
    have H' := congrArg (fun v : Limits.pullback f p ⟶ YB ↦
      (pullbackSymmetry p f).hom ≫ v) Hfst
    simpa only [← Category.assoc, pullbackSymmetry_hom_comp_fst] using H'
  have : ∀ {j k : Over i} (h : j ⟶ k), IsAffineHom (F.map h).left :=
    fun h ↦ inferInstanceAs (IsAffineHom (D.map h.left))
  have : ∀ j : Over i, CompactSpace (F.obj j).left :=
    fun j ↦ inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ {j k : Over i} (h : j ⟶ k),
      IsAffineHom ((AffineTransitionHom.diagram F f).map h) :=
    fun h ↦ AffineTransitionHom.diagram_map_isAffineHom F f h
  have : ∀ j : Over i, CompactSpace ((AffineTransitionHom.diagram F f).obj j) :=
    AffineTransitionHom.diagram_obj_compactSpace F f
  let k₀ : Over i := Over.mk (𝟙 i)
  let u : (AffineTransitionHom.diagram F f).obj k₀ ⟶ YB :=
    Limits.pullback.snd (F.obj k₀).hom f ≫ a₀
  let v : (AffineTransitionHom.diagram F f).obj k₀ ⟶ YB :=
    Limits.pullback.snd (F.obj k₀).hom f ≫ b₀
  have hu : (AffineTransitionHom.projection F f).app k₀ = u ≫ g := by
    change Limits.pullback.snd (F.obj k₀).hom f ≫ f =
      (Limits.pullback.snd (F.obj k₀).hom f ≫ a₀) ≫ g
    rw [Category.assoc, ha₀]
  have hv : (AffineTransitionHom.projection F f).app k₀ = v ≫ g := by
    change Limits.pullback.snd (F.obj k₀).hom f ≫ f =
      (Limits.pullback.snd (F.obj k₀).hom f ≫ b₀) ≫ g
    rw [Category.assoc, hb₀]
  have huv : (AffineTransitionHom.cone F s f).π.app k₀ ≫ u =
      (AffineTransitionHom.cone F s f).π.app k₀ ≫ v := by
    dsimp only [u, v]
    rw [← Category.assoc, AffineTransitionHom.cone_map_snd,
      ← Category.assoc, AffineTransitionHom.cone_map_snd]
    exact hraw
  obtain ⟨j, hj, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (AffineTransitionHom.diagram F f) (AffineTransitionHom.projection F f)
    g (AffineTransitionHom.cone F s f)
    (AffineTransitionHom.coneIsLimit F s (Over.isLimitConePost i hc) f)
    u v hu hv huv
  have hmap : (AffineTransitionHom.diagram F f).map hj ≫
      Limits.pullback.snd (F.obj k₀).hom f =
        Limits.pullback.snd (F.obj j).hom f :=
    Over.w ((Over.pullback f).map (F.map hj))
  change (AffineTransitionHom.diagram F f).map hj ≫
      (Limits.pullback.snd (F.obj k₀).hom f ≫ a₀) =
    (AffineTransitionHom.diagram F f).map hj ≫
      (Limits.pullback.snd (F.obj k₀).hom f ≫ b₀) at heq
  rw [← Category.assoc, hmap, ← Category.assoc, hmap] at heq
  change Limits.pullback.snd (D.map j.hom) f ≫ a₀ =
    Limits.pullback.snd (D.map j.hom) f ≫ b₀ at heq
  have H := congrArg (fun v : Limits.pullback (D.map j.hom) f ⟶ YB ↦
    (pullbackSymmetry (D.map j.hom) f).inv ≫ v) heq
  have Hfst : Limits.pullback.fst f (D.map j.hom) ≫ a₀ =
      Limits.pullback.fst f (D.map j.hom) ≫ b₀ := by
    simpa only [← Category.assoc, pullbackSymmetry_inv_comp_snd] using H
  refine ⟨j.left, j.hom, ?_⟩
  apply Over.OverMorphism.ext
  change Limits.pullback.lift (f := g) (g := D.map j.hom)
      (Limits.pullback.fst f (D.map j.hom) ≫ a₀)
      (Limits.pullback.snd f (D.map j.hom)) _ =
    Limits.pullback.lift (f := g) (g := D.map j.hom)
      (Limits.pullback.fst f (D.map j.hom) ≫ b₀)
      (Limits.pullback.snd f (D.map j.hom)) _
  apply Limits.pullback.hom_ext
  · exact (Limits.pullback.lift_fst _ _ _).trans
      (Hfst.trans (Limits.pullback.lift_fst _ _ _).symm)
  · exact (Limits.pullback.lift_snd _ _ _).trans
      (Limits.pullback.lift_snd _ _ _).symm

private theorem map_eq_of_comparison
    {C₀ C₁ : Type*} [Category* C₀] [Category* C₁]
    {F G : C₀ ⥤ C₁} (e : F ≅ G) {A B : C₀} (a b : A ⟶ B)
    (h : G.map a = G.map b) : F.map a = F.map b := by
  apply (cancel_mono (e.hom.app B)).mp
  rw [e.hom.naturality, e.hom.naturality, h]

/-- A finite family of relative-scheme equations holds after one common
transition when it holds after pullback to the actual limit. -/
theorem exists_over_map_eq_later_stage_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) {K : Type v} [Finite K] (A B : K → Over (D.obj i))
    [∀ k : K, QuasiCompact (A k).hom] [∀ k : K, LocallyOfFiniteType (B k).hom]
    (a b : ∀ k : K, A k ⟶ B k)
    (hab : ∀ k : K, (Over.pullback (c.π.app i)).map (a k) =
      (Over.pullback (c.π.app i)).map (b k)) :
    ∃ (j : I) (hji : j ⟶ i), ∀ k : K,
      (Over.pullback (D.map hji)).map (a k) =
        (Over.pullback (D.map hji)).map (b k) := by
  classical
  choose j hji heq using fun k : K ↦
    exists_over_map_eq_later_stage D c hc i (a k) (b k) (hab k)
  obtain ⟨l, hli, hlj, hcomp⟩ := IsCofiltered.wideCospan hji
  refine ⟨l, hli, ?_⟩
  intro k
  have hmap : D.map hli = D.map (hlj k) ≫ D.map (hji k) := by
    rw [← D.map_comp, hcomp k]
  let e : Over.pullback (D.map hli) ≅
      Over.pullback (D.map (hji k)) ⋙ Over.pullback (D.map (hlj k)) :=
    eqToIso (congrArg (fun f : D.obj l ⟶ D.obj i ↦ Over.pullback f) hmap) ≪≫
      Over.pullbackComp (D.map (hlj k)) (D.map (hji k))
  exact map_eq_of_comparison e (a k) (b k)
    (congrArg (Over.pullback (D.map (hlj k))).map (heq k))

end AlgebraicGeometry.AffineTransitionHom
