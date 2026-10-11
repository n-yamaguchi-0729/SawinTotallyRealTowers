/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_bijective_smul_unit_app_of_bijective_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
Pullback preserves the property that multiplication by a section gives a bijection on sections
over every open subset of a prescribed open.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_bijective_smul_unit_app_of_bijective_smul

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry

open Opposite TopologicalSpace

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace FramePullback

scoped instance opensMap_final' {X Y : Scheme.{u}} (f : X ⟶ Y) : (Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

variable {Z : Scheme.{u}}

/-- The unit sheaf of modules on a scheme. -/
noncomputable def unitMod (Z : Scheme.{u}) : Z.Modules := SheafOfModules.unit Z.ringCatSheaf

/-- Restrict a module section along an inclusion of open subsets. -/
noncomputable abbrev res (N : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (s : Γ(N, W)) : Γ(N, W') :=
  N.presheaf.map (homOfLE h).op s

/-- Restrict a global module section to an open subset. -/
noncomputable abbrev resTop (N : Z.Modules) (W : Z.Opens) (s : Γ(N, ⊤)) : Γ(N, W) :=
  N.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s

lemma res_res (N : Z.Modules) {W₁ W₂ W₃ : Z.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : Γ(N, W₁)) :
    res N h₃₂ (res N h₂₁ s) = res N (h₃₂.trans h₂₁) s := by
  change (N.presheaf.map (homOfLE h₂₁).op ≫ N.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← CategoryTheory.Functor.map_comp]
  rfl

lemma res_resTop (N : Z.Modules) {W W' : Z.Opens} (h : W' ≤ W) (s : Γ(N, ⊤)) :
    res N h (resTop N W s) = resTop N W' s :=
  res_res N le_top h s

lemma res_eq_map (N : Z.Modules) {W' W : Z.Opens} (f : W' ⟶ W) (s : Γ(N, W)) :
    N.presheaf.map f.op s = res N f.le s := by
  rw [Subsingleton.elim f (homOfLE f.le)]

lemma res_smul (N : Z.Modules) {W' W : Z.Opens} (h : W' ≤ W) (r : Γ(Z, W)) (x : Γ(N, W)) :
    res N h (r • x) = Z.presheaf.map (homOfLE h).op r • res N h x :=
  Modules.map_smul N (homOfLE h) r x

lemma app_res {N N' : Z.Modules} (φ : N ⟶ N') {W' W : Z.Opens} (h : W' ≤ W) (s : Γ(N, W)) :
    φ.app W' (res N h s) = res N' h (φ.app W s) := by
  have hnat := φ.mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat s
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  exact hx

/-- The morphism from the unit module obtained by multiplying by a global section. -/
noncomputable def smulHom (N : Z.Modules) (s : Γ(N, ⊤)) : unitMod Z ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (X := Γ(Z, W.unop)) (Y := Γ(N, W.unop))
        { toFun := fun g : Γ(Z, W.unop) => g • resTop N W.unop s
          map_zero' := zero_smul _ _
          map_add' := fun g g' => add_smul g g' _ }
      naturality := fun {W W'} f => by
        have hf : f = (homOfLE f.unop.le).op := congrArg Quiver.Hom.op (Subsingleton.elim _ _)
        rw [hf]
        ext g
        change ((Z.presheaf.map (homOfLE f.unop.le).op : Γ(Z, W.unop) ⟶ Γ(Z, W'.unop)) g) •
            resTop N W'.unop s =
          res N f.unop.le ((show Γ(Z, W.unop) from g) • resTop N W.unop s)
        rw [res_smul, res_resTop] }
    (fun W (r : Γ(Z, W.unop)) (g : Γ(Z, W.unop)) => by
      change (r * g) • resTop N W.unop s = r • (g • resTop N W.unop s)
      exact mul_smul r g _)⟩

lemma smulHom_app_apply (N : Z.Modules) (s : Γ(N, ⊤)) (W : Z.Opens) (g : Γ(Z, W)) :
    (smulHom N s).app W (show Γ(unitMod Z, W) from g) = g • resTop N W s :=
  rfl

lemma isIso_restrict_smulHom (N : Z.Modules) (s : Γ(N, ⊤)) {V : Z.Opens}
    (hs : ∀ W : Z.Opens, W ≤ V → Function.Bijective fun g : Γ(Z, W) => g • resTop N W s) :
    IsIso ((Modules.restrictFunctor V.ι).map (smulHom N s)) := by
  rw [Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso ((smulHom N s).app (V.ι ''ᵁ W))
  rw [ConcreteCategory.isIso_iff_bijective]
  exact hs (V.ι ''ᵁ W) (V.ι_image_le W)

lemma isIso_pullback_smulHom (N : Z.Modules) (s : Γ(N, ⊤)) {V : Z.Opens}
    (hs : ∀ W : Z.Opens, W ≤ V → Function.Bijective fun g : Γ(Z, W) => g • resTop N W s) :
    IsIso ((Modules.pullback V.ι).map (smulHom N s)) :=
  (NatIso.isIso_map_iff (Modules.restrictFunctorIsoPullback V.ι) (smulHom N s)).mp
    (isIso_restrict_smulHom N s hs)

section pullback

variable {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules)

private theorem nativePushforwardRightAdjoint :
    (SheafOfModules.pushforward.{u} p.toRingCatSheafHom).IsRightAdjoint :=
  (Modules.pullbackPushforwardAdjunction p).isRightAdjoint

attribute [local instance] nativePushforwardRightAdjoint

/-- The pullback of `M` along `p`. -/
noncomputable abbrev F : X'.Modules := (Modules.pullback p).obj M

/-- The section of the pullback module induced by the pullback-pushforward adjunction unit. -/
noncomputable def eta (U : X.Opens) (m : Γ(M, U)) : Γ(F p M, p ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction p).unit.app M).app U m

lemma eta_smul (U : X.Opens) (r : Γ(X, U)) (m : Γ(M, U)) :
    eta p M U (r • m) = p.app U r • eta p M U m :=
  Modules.Hom.app_smul _ r m

lemma res_eta {U U' : X.Opens} (h : U' ≤ U) (m : Γ(M, U)) :
    res (F p M) (p.preimage_mono h) (eta p M U m) = eta p M U' (res M h m) := by
  have hnat := ((pullbackPushforwardAdjunction p).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hnat m
  simp only [ConcreteCategory.comp_apply, mapPresheaf_app] at hx
  exact ((res_eq_map (F p M) ((Opens.map p.base).map (homOfLE h)) _).symm).trans hx.symm

lemma isIso_pullback_pullback_smulHom (s : Γ(M, ⊤)) {V : X.Opens}
    (hs : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) => g • resTop M W s) :
    IsIso ((Modules.pullback (p ⁻¹ᵁ V).ι).map ((Modules.pullback p).map (smulHom M s))) := by
  have hfact : (p ⁻¹ᵁ V).ι ≫ p = (p ∣_ V) ≫ V.ι := (morphismRestrict_ι p V).symm
  let e : Modules.pullback p ⋙ Modules.pullback (p ⁻¹ᵁ V).ι ≅
      Modules.pullback V.ι ⋙ Modules.pullback (p ∣_ V) :=
    Modules.pullbackComp _ _ ≪≫ Modules.pullbackCongr hfact ≪≫ (Modules.pullbackComp _ _).symm
  have h1 : IsIso ((Modules.pullback V.ι ⋙ Modules.pullback (p ∣_ V)).map (smulHom M s)) := by
    change IsIso ((Modules.pullback (p ∣_ V)).map ((Modules.pullback V.ι).map (smulHom M s)))
    have := isIso_pullback_smulHom M s hs
    infer_instance
  exact (NatIso.isIso_map_iff e (smulHom M s)).mpr h1

/-- The canonical identification of the pullback of the unit module with the unit module. -/
noncomputable def unitIso : (Modules.pullback p).obj (unitMod X) ≅ unitMod X' := by
  let : (Opens.map p.base).Final := opensMap_final' p
  let makeUnitIso {C D : Type u} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
      {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
      [Functor.IsContinuous F J K]
      (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
      [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] [F.Final] :
      (SheafOfModules.pullback φ).obj (SheafOfModules.unit S) ≅ SheafOfModules.unit R :=
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  exact makeUnitIso p.toRingCatSheafHom

lemma unitIso_hom :
    (unitIso p).hom = SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom := rfl

lemma unitIso_hom_comp_smulHom (s : Γ(M, ⊤)) :
    (unitIso p).hom ≫ smulHom (F p M) (eta p M ⊤ s) = (Modules.pullback p).map (smulHom M s) := by
  apply ((pullbackPushforwardAdjunction p).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hu : (pullbackPushforwardAdjunction p).unit.app _ ≫
      (Modules.pushforward p).map (unitIso p).hom =
      SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom := by
    have := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      p.toRingCatSheafHom
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have h' : (pullbackPushforwardAdjunction p).unit.app _ ≫
      (Modules.pushforward p).map ((unitIso p).hom ≫ smulHom (F p M) (eta p M ⊤ s)) =
        SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
          (Modules.pushforward p).map (smulHom (F p M) (eta p M ⊤ s)) := by
    rw [← hu]
    rfl
  have hn := (pullbackPushforwardAdjunction p).unit.naturality (smulHom M s)
  have KEY : SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom ≫
      (Modules.pushforward p).map (smulHom (F p M) (eta p M ⊤ s)) =
        smulHom M s ≫ (pullbackPushforwardAdjunction p).unit.app M := by
    refine Modules.hom_ext _ _ fun W => ?_
    ext g
    let s' : Γ(F p M, ⊤) := eta p M ⊤ s
    have hg : (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom).val.app (op W) g =
        p.app W (show Γ(X, W) from g) :=
      SheafOfModules.unitToPushforwardObjUnit_val_app_apply p.toRingCatSheafHom (X := op W)
        (show Γ(X, W) from g)
    have hleft := congrArg
      (fun z : Γ(X', p ⁻¹ᵁ W) => (smulHom (F p M) s').app (p ⁻¹ᵁ W) z) hg
    have hrestrict : resTop (F p M) (p ⁻¹ᵁ W) s' = eta p M W (resTop M W s) :=
      res_eta p M le_top s
    have hvalue : (p.app W (show Γ(X, W) from g)) • resTop (F p M) (p ⁻¹ᵁ W) s' =
        eta p M W ((show Γ(X, W) from g) • resTop M W s) :=
      (congrArg (fun z : Γ(F p M, p ⁻¹ᵁ W) => (p.app W (show Γ(X, W) from g)) • z)
        hrestrict).trans (eta_smul p M W (show Γ(X, W) from g) (resTop M W s)).symm
    exact hleft.trans ((smulHom_app_apply (F p M) s' (p ⁻¹ᵁ W)
      (p.app W (show Γ(X, W) from g))).trans hvalue)
  exact h'.trans (KEY.trans hn)

lemma smulHom_eta_eq (s : Γ(M, ⊤)) :
    smulHom (F p M) (eta p M ⊤ s) = (unitIso p).inv ≫ (Modules.pullback p).map (smulHom M s) := by
  rw [← unitIso_hom_comp_smulHom, Iso.inv_hom_id_assoc]

lemma isIso_pullback_smulHom_eta (s : Γ(M, ⊤)) {V : X.Opens}
    (hs : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) => g • resTop M W s) :
    IsIso ((Modules.pullback (p ⁻¹ᵁ V).ι).map (smulHom (F p M) (eta p M ⊤ s))) := by
  rw [smulHom_eta_eq, CategoryTheory.Functor.map_comp]
  have := isIso_pullback_pullback_smulHom p M s hs
  infer_instance

omit M in
lemma image_preimage_eq {W V : X'.Opens} (hW : W ≤ V) : V.ι ''ᵁ (V.ι ⁻¹ᵁ W) = W :=
  (Scheme.Hom.image_preimage_eq_opensRange_inf V.ι W).trans
    (by rw [Scheme.Opens.opensRange_ι]; exact inf_eq_right.mpr hW)

theorem main (s : Γ(M, ⊤)) {V : X.Opens}
    (hs : ∀ W : X.Opens, W ≤ V → Function.Bijective fun g : Γ(X, W) => g • resTop M W s)
    (W' : X'.Opens) (hW' : W' ≤ p ⁻¹ᵁ V) :
    Function.Bijective fun g : X'.presheaf.obj (op W') => g • resTop (F p M) W' (eta p M ⊤ s) := by
  have h1 := isIso_pullback_smulHom_eta p M s hs
  have h2 : IsIso ((Modules.restrictFunctor (p ⁻¹ᵁ V).ι).map (smulHom (F p M) (eta p M ⊤ s))) :=
    (NatIso.isIso_map_iff (Modules.restrictFunctorIsoPullback (p ⁻¹ᵁ V).ι) _).mpr h1
  rw [Modules.Hom.isIso_iff_isIso_app] at h2
  have h3 : IsIso ((smulHom (F p M) (eta p M ⊤ s)).app ((p ⁻¹ᵁ V).ι ''ᵁ ((p ⁻¹ᵁ V).ι ⁻¹ᵁ W'))) :=
    h2 ((p ⁻¹ᵁ V).ι ⁻¹ᵁ W')
  rw [image_preimage_eq hW'] at h3
  exact (ConcreteCategory.bijective_of_isIso ((smulHom (F p M) (eta p M ⊤ s)).app W'))

end pullback

end FramePullback

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.bijective_smul_unit_app_of_bijective_smul
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (σ : Γ(M, ⊤)) {V : X.Opens}
    (hσ : ∀ W : X.Opens, W ≤ V →
      Function.Bijective fun g : Γ(X, W) =>
        g • (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op σ : Γ(M, W)))
    (W' : X'.Opens) (hW' : W' ≤ p ⁻¹ᵁ V) :
    Function.Bijective fun g : Γ(X', W') =>
      g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op
        ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) σ) :
          Γ((Scheme.Modules.pullback p).obj M, W')) :=
  AlgebraicGeometry.Scheme.Modules.FramePullback.main p M σ hσ W' hW'
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_bijective_smul_unit_app_of_bijective_smul
end ProofImplementation
