/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesRestrictOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Pushforward transformations and adjunctions for module presheaves

Constructs transformations and adjunctions from the corresponding indexing functors
and compatible morphisms of ring presheaves.
-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

namespace PresheafOfModules

section NatTrans

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G H : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}
  (φ : T ⟶ G.op ⋙ S)


/-- The transformation between module pushforwards induced by a transformation of the indexing
  functors. -/
noncomputable def pushforwardNatTrans (α : F ⟶ G) :
    pushforward.{v} φ ⟶ pushforward.{v} (F := F) (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M :=
  { app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      dsimp
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← CategoryTheory.Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app_apply (α : F ⟶ G) (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

/-- The isomorphism between module pushforwards along equal morphisms of ring presheaves. -/
noncomputable def pushforwardCongr {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents
    (fun M ↦ isoMk
      (fun U ↦ (ModuleCat.restrictScalarsCongr (by subst e; rfl)).app _)
      fun _ _ _ ↦ by subst e; rfl)
    fun _ ↦ by subst e; rfl

@[simp] lemma pushforwardCongr_hom_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).hom.app M).app U x = x := by subst e; rfl

@[simp] lemma pushforwardCongr_inv_app_app_apply {φ ψ : T ⟶ G.op ⋙ S} (e : φ = ψ)
    (M : PresheafOfModules.{v} S) (U x) :
    ((pushforwardCongr e).inv.app M).app U x = x := by subst e; rfl

end NatTrans

section Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {G : D ⥤ C} {S : Cᵒᵖ ⥤ RingCat.{u}} {R : Dᵒᵖ ⥤ RingCat.{u}}
  (adj : F ⊣ G) (φ : S ⟶ F.op ⋙ R) (ψ : R ⟶ G.op ⋙ S)
  (H₁ : whiskerRight (NatTrans.op adj.counit) R = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫ whiskerRight (NatTrans.op adj.unit) S = 𝟙 S)


/-- The adjunction between module pushforwards induced by the given adjunction and its
  compatible ring maps. -/
noncomputable def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit :=
    (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
      (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit :=
    (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
      (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components X := by
    ext U x
    change (X.presheaf.map (adj.counit.app (F.obj U.unop)).op ≫
      X.presheaf.map (F.map (adj.unit.app U.unop)).op) _ = _
    dsimp only [id_obj]
    rw [← Functor.map_comp, ← op_comp, adj.left_triangle_components]
    have hid := X.presheaf.map_id (Opposite.op (F.obj U.unop))
    exact congrArg
      (fun k : X.presheaf.obj (Opposite.op (F.obj U.unop)) ⟶
        X.presheaf.obj (Opposite.op (F.obj U.unop)) => k.hom
          (id x : X.presheaf.obj (Opposite.op (F.obj U.unop)))) hid
  right_triangle_components X := by
    ext U x
    change (X.presheaf.map (G.map (adj.counit.app U.unop)).op ≫
      X.presheaf.map (adj.unit.app (G.obj U.unop)).op) _ = _
    rw [← Functor.map_comp, ← op_comp, adj.right_triangle_components]
    have hid := X.presheaf.map_id (Opposite.op (G.obj U.unop))
    exact congrArg
      (fun k : X.presheaf.obj (Opposite.op (G.obj U.unop)) ⟶
        X.presheaf.obj (Opposite.op (G.obj U.unop)) => k.hom
          (id x : X.presheaf.obj (Opposite.op (G.obj U.unop)))) hid

lemma pushforwardPushforwardAdj_unit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).unit.app M).app U x =
      M.map (adj.counit.app U.unop).op x := rfl

lemma pushforwardPushforwardAdj_counit_app_app_apply (M U x) :
    ((pushforwardPushforwardAdj adj φ ψ H₁ H₂).counit.app M).app U x =
      M.map (adj.unit.app U.unop).op x := rfl

end Adjunction

end PresheafOfModules
