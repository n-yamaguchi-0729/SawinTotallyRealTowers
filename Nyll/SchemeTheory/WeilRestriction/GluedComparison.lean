/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.GluingData
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Comparing glued representers with their local pieces

The cartesian squares of relative gluing identify each local representer
with the pullback of the glued scheme. The resulting hom-set equivalence
has an explicit inverse: compose a local map with its gluing inclusion.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

namespace SchemeTheory.WeilRestriction

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
  (𝒰 : S.OpenCover) [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]
  (W : ∀ i : 𝒰.I₀, Over (𝒰.X i))
  (h : ∀ i : 𝒰.I₀, ((Over.map (𝒰.f i)).op ⋙ F).RepresentableBy (W i))
  [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The local representer maps to the glued scheme over the original base. -/
def gluedLocalRepresenterInclusion (i : 𝒰.I₀) :
    (Over.map (𝒰.f i)).obj (W i) ⟶ gluedLocalRepresenter F 𝒰 W h :=
  Over.homMk (colimit.ι (localRepresenterGluingData F 𝒰 W h).functor i)
    ((localRepresenterGluingData F 𝒰 W h).ι_toBase i)

/-- Pulling the glued scheme back to a cover member recovers its local representer. -/
def gluedLocalRepresenterPullbackIso (i : 𝒰.I₀) :
    W i ≅ (Over.pullback (𝒰.f i)).obj (gluedLocalRepresenter F 𝒰 W h) :=
  Over.isoMk
    ((localRepresenterGluingData F 𝒰 W h).isPullback_natTrans_ι_toBase i).flip.isoPullback
    ((localRepresenterGluingData F 𝒰 W h).isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd

/-- Maps from a test scheme over a cover member into the glued scheme
are equivalent to maps into the corresponding local representer. -/
def gluedLocalRepresenterHomEquiv (i : 𝒰.I₀) (T : Over (𝒰.X i)) :
    ((Over.map (𝒰.f i)).obj T ⟶ gluedLocalRepresenter F 𝒰 W h) ≃ (T ⟶ W i) :=
  ((Over.mapPullbackAdj (𝒰.f i)).homEquiv T (gluedLocalRepresenter F 𝒰 W h)).trans
    (gluedLocalRepresenterPullbackIso F 𝒰 W h i).symm.homToEquiv

/-- The inverse comparison is composition with the gluing inclusion. -/
lemma gluedLocalRepresenterHomEquiv_symm (i : 𝒰.I₀) (T : Over (𝒰.X i))
    (k : T ⟶ W i) :
    (gluedLocalRepresenterHomEquiv F 𝒰 W h i T).symm k =
      (Over.map (𝒰.f i)).map k ≫ gluedLocalRepresenterInclusion F 𝒰 W h i := by
  apply Over.OverMorphism.ext
  let d := localRepresenterGluingData F 𝒰 W h
  let e : (W i).left ≅ pullback d.toBase (𝒰.f i) :=
    (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
  change @Eq (T.left ⟶ colimit d.functor)
    ((k.left ≫ e.hom) ≫
      (𝟙 (pullback d.toBase (𝒰.f i)) ≫
        pullback.fst d.toBase (𝒰.f i)))
    (k.left ≫ colimit.ι (localRepresenterGluingData F 𝒰 W h).functor i)
  rw [Category.id_comp, Category.assoc]
  exact congrArg (fun g : (W i).left ⟶ colimit d.functor => k.left ≫ g)
    (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_fst

end SchemeTheory.WeilRestriction
