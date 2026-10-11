/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeLocality
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Restriction of finite-type sheaves of modules

The covering of a restriction consists of objects mapping both to the
chosen slice object and to a member of the original generating cover.
Each finite family is transported along the actual restriction functor.
-/

noncomputable section

universe u v₁ u₁

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Restrict local generators using all objects which map into the original cover. -/
def LocalGeneratorsData.over {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (U : C) : (M.over U).LocalGeneratorsData where
  I := (V : Over U) × (i : q.I) × (V.left ⟶ q.X i)
  X i := i.1
  coversTop Y := by
    apply (J.over U).superset_covering _
      ((Over.forget U).cover_lift (J.over U) J (q.coversTop Y.left))
    intro Z g hg
    obtain ⟨i, ⟨v⟩⟩ := hg
    exact ⟨⟨Z, i, v⟩, ⟨𝟙 Z⟩⟩
  generators i := by
    let t := (q.generators i.2.1).map (overMap R i.2.2)
      (overMapUnitIso (R := R) i.2.2).symm
    let t' : (M.over i.1.left).GeneratingSections :=
      t.ofEpi ((overFunctorMap R i.2.2).app M).hom
    let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv i.1)
      (S := (R.over U).over i.1) (R := R.over i.1.left) (𝟙 _) (𝟙 _)
      (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
    exact t'.map e.functor (Iso.refl _)

/-- Restriction preserves the finite index type of each local generating family. -/
lemma LocalGeneratorsData.isFiniteType_over {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) (U : C) (hq : q.IsFiniteType) :
    (q.over U).IsFiniteType := by
  constructor
  intro i
  exact ⟨(hq.isFiniteType i.2.1).finite⟩

/-- Restricting an actual finite-type sheaf to an object preserves finite type. -/
lemma IsFiniteType.over (M : SheafOfModules.{u} R) (U : C)
    (hM : M.IsFiniteType) : (M.over U).IsFiniteType := by
  have : M.IsFiniteType := hM
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  exact (q.over U).isFiniteType (q.isFiniteType_over U hq)

end SheafOfModules
