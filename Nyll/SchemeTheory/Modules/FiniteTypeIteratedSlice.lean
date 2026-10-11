/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou; Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypePushforward
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Over

/-!
# Finite type and quasicoherence on iterated slice sites

The actual equivalence between an iterated slice and the slice over its
underlying object transports the local finite generating families. All
site, ring and module structures here use the native slice projections.

The comparison through the iterated-slice equivalence follows the native
quasicoherent-data construction at Mathlib revision
065356127b1dc0016f66b7283ce0ce2c4055aa55:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean
-/

noncomputable section

universe u v₁ v₂ u₁ u₂

open CategoryTheory Limits

namespace SheafOfModules

private theorem post_continuous_of_equivalence
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (e : C ≌ D)
    [e.functor.IsDenseSubsite J K] (W : C) :
    (Over.post (X := W) e.functor).IsContinuous (J.over W) (K.over (e.functor.obj W)) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreservingOfFlat _ (Over.post (X := W) e.functor))
    (CoverPreserving.overPost W (Functor.IsDenseSubsite.coverPreserving J K e.functor))

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y Z, HasSheafify (((J.over X).over Y).over Z) AddCommGrpCat.{u}]
  [∀ X Y Z, (((J.over X).over Y).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Direct finite type transports to the actual iterated restriction. -/
theorem IsFiniteType.iteratedSlice_forward (M : SheafOfModules.{u} R)
    {X : C} (f : Over X) (hM : (M.over f.left).IsFiniteType) :
    ((M.over X).over f).IsFiniteType := by
  have hInverseDense : f.iteratedSliceEquiv.inverse.IsDenseSubsite
      (J.over f.left) ((J.over X).over f) := inferInstance
  have hForwardDense : f.iteratedSliceEquiv.functor.IsDenseSubsite
      ((J.over X).over f) (J.over f.left) := inferInstance
  have : ∀ W : Over f, (Over.post (X := W) f.iteratedSliceEquiv.functor).IsContinuous
      (((J.over X).over f).over W)
      ((J.over f.left).over (f.iteratedSliceEquiv.functor.obj W)) :=
    fun W => post_continuous_of_equivalence
      ((J.over X).over f) (J.over f.left) f.iteratedSliceEquiv W
  let α : (R.over X).over f ≅
      (f.iteratedSliceEquiv.functor.sheafPushforwardContinuous RingCat.{u}
        ((J.over X).over f) (J.over f.left)).obj (R.over f.left) := Iso.refl _
  have hα : IsIso α.hom := α.isIso_hom
  exact isFiniteType_pushforward_of_isLeftAdjoint f.iteratedSliceEquiv.functor
    (R := R.over f.left) (S := (R.over X).over f) α.hom (Iso.refl _) hM

/-- Actual iterated finite type transports to the direct restriction. -/
theorem IsFiniteType.iteratedSlice_backward (M : SheafOfModules.{u} R)
    {X : C} (f : Over X) (hM : ((M.over X).over f).IsFiniteType) :
    (M.over f.left).IsFiniteType := by
  have hInverseDense : f.iteratedSliceEquiv.symm.functor.IsDenseSubsite
      (J.over f.left) ((J.over X).over f) :=
    inferInstanceAs (f.iteratedSliceEquiv.inverse.IsDenseSubsite
      (J.over f.left) ((J.over X).over f))
  have : ∀ W : Over f.left, (Over.post (X := W) f.iteratedSliceEquiv.inverse).IsContinuous
      ((J.over f.left).over W)
      (((J.over X).over f).over (f.iteratedSliceEquiv.inverse.obj W)) :=
    fun W => post_continuous_of_equivalence
      (J.over f.left) ((J.over X).over f) f.iteratedSliceEquiv.symm W
  let α : (R.over X).over f ≅
      (f.iteratedSliceEquiv.functor.sheafPushforwardContinuous RingCat.{u}
        ((J.over X).over f) (J.over f.left)).obj (R.over f.left) := Iso.refl _
  let β : R.over f.left ≅
      (f.iteratedSliceEquiv.inverse.sheafPushforwardContinuous RingCat.{u}
        (J.over f.left) ((J.over X).over f)).obj ((R.over X).over f) := Iso.refl _
  let E := pushforwardPushforwardEquivalence f.iteratedSliceEquiv
    (S := (R.over X).over f) (R := R.over f.left) α.hom β.hom
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
  have hβ : IsIso β.hom := β.isIso_hom
  have hDirect : (E.inverse.obj ((M.over X).over f)).IsFiniteType :=
    isFiniteType_pushforward_of_isLeftAdjoint f.iteratedSliceEquiv.inverse
      (R := (R.over X).over f) (S := R.over f.left) β.hom (Iso.refl _) hM
  let t : E.inverse.obj ((M.over X).over f) ≅ M.over f.left :=
    E.fullyFaithfulFunctor.preimageIso
      (by exact E.counitIso.app ((M.over X).over f))
  exact IsFiniteType.of_iso (R := R.over f.left) t hDirect

/-- Direct quasicoherence transports to the actual iterated restriction. -/
theorem isQuasicoherent_iteratedSlice_forward (M : SheafOfModules.{u} R)
    {X : C} (f : Over X) (hM : (M.over f.left).IsQuasicoherent) :
    ((M.over X).over f).IsQuasicoherent := by
  have hInverseDense : f.iteratedSliceEquiv.inverse.IsDenseSubsite
      (J.over f.left) ((J.over X).over f) := inferInstance
  have hForwardDense : f.iteratedSliceEquiv.functor.IsDenseSubsite
      ((J.over X).over f) (J.over f.left) := inferInstance
  have : ∀ W : Over f, (Over.post (X := W) f.iteratedSliceEquiv.functor).IsContinuous
      (((J.over X).over f).over W)
      ((J.over f.left).over (f.iteratedSliceEquiv.functor.obj W)) :=
    fun W => post_continuous_of_equivalence
      ((J.over X).over f) (J.over f.left) f.iteratedSliceEquiv W
  have : (M.over f.left).IsQuasicoherent := hM
  let α : (R.over X).over f ≅
      (f.iteratedSliceEquiv.functor.sheafPushforwardContinuous RingCat.{u}
        ((J.over X).over f) (J.over f.left)).obj (R.over f.left) := Iso.refl _
  have hα : IsIso α.hom := α.isIso_hom
  exact isQuasicoherent_pushforward_of_isLeftAdjoint f.iteratedSliceEquiv.functor
    (R := R.over f.left) (S := (R.over X).over f) (M := M.over f.left)
    α.hom (Iso.refl _)

end SheafOfModules
