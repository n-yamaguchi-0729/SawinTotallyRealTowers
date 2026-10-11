/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou; Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeLocality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Transport of finite type along restriction functors

Cover lifting and the actual maps of generating sections transport finite
type through continuous and cocontinuous functors. This supplies the
iterated-slice and subopen restrictions needed for gluing on a union.

The cover-lifting construction and local adjunction argument are adapted
from Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent at the pinned
revision 065356127b1dc0016f66b7283ce0ce2c4055aa55:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
-/

noncomputable section

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} {D : Type u₂} [Category.{v₂} D]
  {K : GrothendieckTopology D} {S : Sheaf K RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
  (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)

/-- Lift the original cover and map its actual generating families. -/
def LocalGeneratorsData.pushforward (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) :
    ((SheafOfModules.pushforward φ).obj M).LocalGeneratorsData where
  I := (X : D) × (i : q.I) × (G.obj X ⟶ q.X i)
  X i := i.1
  coversTop Y := by
    refine K.superset_covering ?_ (G.cover_lift K J (q.coversTop (G.obj Y)))
    intro Z g hg
    obtain ⟨i, ⟨v⟩⟩ := hg
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 Z⟩⟩
  generators i := by
    let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
      SheafOfModules.pushforward (𝟙 _)
    let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
    let ψ : S.over i.1 ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1) (J.over (q.X i.2.1))).obj
          (R.over (q.X i.2.1)) :=
      ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
    let e : (SheafOfModules.pushforward ψ).obj (unit (R.over (q.X i.2.1))) ≅ unit (S.over i.1) :=
      overS.mapIso η
    have : PreservesColimitsOfSize.{u, u} (SheafOfModules.pushforward ψ) := h _ _ _
    exact (q.generators i.2.1).map (SheafOfModules.pushforward ψ) e.symm

/-- Every transported local generating family has its original finite index type. -/
lemma LocalGeneratorsData.isFiniteType_pushforward
    (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} (q : M.LocalGeneratorsData) (hq : q.IsFiniteType) :
    (q.pushforward G φ η h).IsFiniteType := by
  constructor
  intro i
  exact ⟨(hq.isFiniteType i.2.1).finite⟩

/-- A restriction functor preserving the unit and local colimits preserves finite type. -/
lemma isFiniteType_pushforward_of_isLeftAdjoint
    (η : (SheafOfModules.pushforward φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over _)]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} (hM : M.IsFiniteType) :
    ((SheafOfModules.pushforward φ).obj M).IsFiniteType := by
  have h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (SheafOfModules.pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)) := by
    intro X Y f
    let G' := Over.post (X := X) G ⋙ Over.map f
    have : G'.IsContinuous (K.over X) (J.over Y) :=
      Functor.isContinuous_comp _ _ _ (J.over _) _
    have : G'.IsCocontinuous (K.over X) (J.over Y) :=
      isCocontinuous_comp _ _ _ (J.over _)
    let a : S.over X ⟶
        (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
      ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
    have : IsIso a := inferInstanceAs
      (IsIso (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ))
    have : (SheafOfModules.pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
    exact inferInstanceAs (PreservesColimitsOfSize.{u, u} (SheafOfModules.pushforward.{u} a))
  have : M.IsFiniteType := hM
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  exact (q.pushforward G φ η h).isFiniteType
    (q.isFiniteType_pushforward G φ η h hq)

end SheafOfModules
