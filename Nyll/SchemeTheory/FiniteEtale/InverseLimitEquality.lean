/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
# Eventual equality of native finite-etale morphisms

Equality after pullback to the actual inverse limit is detected by a genuine
later stage. The maps in the conclusion are the native finite-etale pullback
maps, so the result applies directly to inverse and cocycle equations.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

/-- Two morphisms of finite-etale covers whose native pullbacks to the limit
agree have equal native pullbacks at a later original stage. -/
theorem exists_inverse_limit_stage_map_eq
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, CompactSpace (D.obj i)]
    (i : I) {A B : FiniteEtale (D.obj i)} (a b : A ⟶ B)
    (hab : (FiniteEtale.pullback (c.π.app i)).map a =
      (FiniteEtale.pullback (c.π.app i)).map b) :
    ∃ (j : I) (hji : j ⟶ i),
      (FiniteEtale.pullback (D.map hji)).map a =
        (FiniteEtale.pullback (D.map hji)).map b := by
  let YA : Scheme.{u} := A.left
  let YB : Scheme.{u} := B.left
  let f : YA ⟶ D.obj i := A.hom
  let g : YB ⟶ D.obj i := B.hom
  have : IsFiniteEtale f := A.prop
  have : IsFiniteEtale g := B.prop
  let F : Over i ⥤ Over (D.obj i) := Over.post D
  let s : Cone F := (Over.conePost D i).obj c
  let p : c.pt ⟶ D.obj i := c.π.app i
  let a₀ : YA ⟶ YB := a.left
  let b₀ : YA ⟶ YB := b.left
  have ha₀ : a₀ ≫ g = f := MorphismProperty.Over.w a
  have hb₀ : b₀ ≫ g = f := MorphismProperty.Over.w b
  have hraw : Limits.pullback.snd p f ≫ a₀ =
      Limits.pullback.snd p f ≫ b₀ := by
    have H := congrArg (fun v ↦ v.left) hab
    have haproj : ((FiniteEtale.pullback p).map a).left ≫ Limits.pullback.fst g p =
        Limits.pullback.fst f p ≫ a₀ := Limits.pullback.lift_fst _ _ _
    have hbproj : ((FiniteEtale.pullback p).map b).left ≫ Limits.pullback.fst g p =
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
  apply MorphismProperty.Over.Hom.ext
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

end AlgebraicGeometry.FiniteEtale
