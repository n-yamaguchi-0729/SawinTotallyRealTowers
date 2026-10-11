/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesPushforwardRestrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Tactic.Ext

/-!
# Restriction of direct images to open subschemes

The comparison uses the actual preimage-open equality and native scheme
restriction maps. The former AlgebraicCurves owner reexports this shared owner.
-/

universe u

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private lemma topSheaf_comp_hom {Z : TopCat.{u}}
    {A B C : Z.Sheaf RingCat.{u}} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y) (W : Y.Opens)

/-- The two actual target-open indexing functors agree by the preimage formula for
`morphismRestrict`. -/
noncomputable def restrictPushforwardOpensIso :
    (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor : W.toScheme.Opens ⥤ X.Opens) ≅
      W.ι.opensFunctor ⋙ Opens.map g.base :=
  NatIso.ofComponents (fun U => eqToIso (image_morphismRestrict_preimage g W U))
    (fun _ => Subsingleton.elim _ _)
/-- Restriction to an open subscheme commutes with the actual direct image.
The ring-map comparison is proved from `morphismRestrict_app'`. -/
noncomputable def pushforwardRestrictIso :
    restrictFunctor (g ⁻¹ᵁ W).ι ⋙ pushforward (g ∣_ W) ≅ pushforward g ⋙ restrictFunctor W.ι :=
  let : Functor.IsContinuous
      (Opens.map (g ∣_ W).base ⋙ (g ⁻¹ᵁ W).ι.opensFunctor)
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology X) :=
    CategoryTheory.Functor.isContinuous_comp.{u} (Opens.map (g ∣_ W).base)
      (g ⁻¹ᵁ W).ι.opensFunctor
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology ↑(g ⁻¹ᵁ W))
      (Opens.grothendieckTopology X)
  let : Functor.IsContinuous (W.ι.opensFunctor ⋙ Opens.map g.base)
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology X) :=
    CategoryTheory.Functor.isContinuous_comp.{u} W.ι.opensFunctor (Opens.map g.base)
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  by
    refine SheafOfModules.pushforwardComp _ _ ≪≫
      SheafOfModules.pushforwardNatIso _ (restrictPushforwardOpensIso g W).symm ≪≫ ?_ ≪≫
      (SheafOfModules.pushforwardComp _ _).symm
    refine SheafOfModules.pushforwardCongr ?_
    let α' : (g ⁻¹ᵁ W).toScheme.presheaf ⟶
        (g ⁻¹ᵁ W).ι.opensFunctor.op ⋙ X.presheaf :=
      { app U := ((g ⁻¹ᵁ W).ι.appIso U.unop).inv }
    let β' : W.toScheme.presheaf ⟶ W.ι.opensFunctor.op ⋙ Y.presheaf :=
      { app U := (W.ι.appIso U.unop).inv }
    let α : (g ⁻¹ᵁ W).toScheme.ringCatSheaf ⟶
        ((g ⁻¹ᵁ W).ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology (g ⁻¹ᵁ W))
          (Opens.grothendieckTopology X)).obj X.ringCatSheaf :=
      ⟨Functor.whiskerRight α' (forget₂ CommRingCat RingCat)⟩
    let β : W.toScheme.ringCatSheaf ⟶
        (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology W)
          (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
      ⟨Functor.whiskerRight β' (forget₂ CommRingCat RingCat)⟩
    let a := (g ∣_ W).toRingCatSheafHom
    let b := ((Opens.map (g ∣_ W).base).sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology W)
      (Opens.grothendieckTopology (g ⁻¹ᵁ W))).map α
    let c := (Functor.sheafPushforwardContinuousNatTrans
      (restrictPushforwardOpensIso g W).inv RingCat.{u}
      (Opens.grothendieckTopology W) (Opens.grothendieckTopology X)).app X.ringCatSheaf
    let d := (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology W)
      (Opens.grothendieckTopology Y)).map g.toRingCatSheafHom
    have hab : (a ≫ b).hom = a.hom ≫ b.hom := topSheaf_comp_hom a b
    have habc : ((a ≫ b) ≫ c).hom = (a ≫ b).hom ≫ c.hom :=
      topSheaf_comp_hom (a ≫ b) c
    have hβd : (β ≫ d).hom = β.hom ≫ d.hom := topSheaf_comp_hom β d
    have hb : b.hom = Functor.whiskerLeft (Opens.map (g ∣_ W).base).op α.hom := rfl
    have hd : d.hom = Functor.whiskerLeft W.ι.opensFunctor.op g.toRingCatSheafHom.hom := rfl
    have hcomponent : (a.hom ≫ b.hom) ≫ c.hom = β.hom ≫ d.hom := by
      rw [hb, hd]
      ext U x
      dsimp only [a, c, α, β, α', β', Hom.toRingCatSheafHom,
        Functor.sheafPushforwardContinuousNatTrans, restrictPushforwardOpensIso]
      simp only [Opens.ι_appIso, Iso.refl_inv]
      change (X.presheaf.map (eqToHom
        (image_morphismRestrict_preimage g W U.unop).symm).op)
          ((g ∣_ W).app U.unop x) = g.app (W.ι ''ᵁ U.unop) x
      rw [morphismRestrict_app']
      erw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]
      rfl
    apply ObjectProperty.hom_ext
    exact Eq.trans habc (Eq.trans (congrArg (fun k => k ≫ c.hom) hab)
      (Eq.trans hcomponent hβd.symm))

lemma pushforwardRestrictIso_hom_app_app (M : X.Modules) (U : W.toScheme.Opens) :
    ((pushforwardRestrictIso g W).hom.app M).app U =
      M.presheaf.map (eqToHom (image_morphismRestrict_preimage g W U).symm).op := by
  rfl

end AlgebraicGeometry.Scheme.Modules
