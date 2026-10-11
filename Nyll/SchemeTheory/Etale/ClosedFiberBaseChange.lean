/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.ResidueFieldPushout
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual closed fibres under a local base change

The closed fibre after a local base change is the base change of the original
closed fibre along the canonical residue-field map. When the extended
maximal ideal is the new maximal ideal, it is also the base change of the
original closed-fibre inclusion over the original base. Both comparisons
use the actual pullback maps and retain their projection equations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

local notation "baseMap" => Spec.map (CommRingCat.ofHom (algebraMap A B))
local notation "residueA" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))
local notation "residueB" => Spec.map (CommRingCat.ofHom (IsLocalRing.residue B))
local notation "residueMap" =>
  Spec.map (CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap A B)))

private lemma residue_square : residueB ≫ baseMap = residueMap ≫ residueA := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, IsLocalRing.ResidueField.map_comp_residue]

/-- The canonical map from the new closed fibre to the old closed fibre. -/
def closedFiberBaseChangeMap :
    pullback (pullback.snd f baseMap) residueB ⟶ pullback f residueA :=
  pullback.lift
    (pullback.fst (pullback.snd f baseMap) residueB ≫ pullback.fst f baseMap)
    (pullback.snd (pullback.snd f baseMap) residueB ≫ residueMap) (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, residue_square (A := A) (B := B), ← Category.assoc])

@[reassoc]
lemma closedFiberBaseChangeMap_fst :
    closedFiberBaseChangeMap (B := B) f ≫ pullback.fst f residueA =
      pullback.fst (pullback.snd f baseMap) residueB ≫ pullback.fst f baseMap :=
  pullback.lift_fst _ _ _

@[reassoc]
lemma closedFiberBaseChangeMap_snd :
    closedFiberBaseChangeMap (B := B) f ≫ pullback.snd f residueA =
      pullback.snd (pullback.snd f baseMap) residueB ≫ residueMap :=
  pullback.lift_snd _ _ _

/-- The canonical closed-fibre comparison is cartesian over the residue fields. -/
lemma isPullback_closedFiberBaseChangeMap :
    IsPullback (closedFiberBaseChangeMap (B := B) f)
      (pullback.snd (pullback.snd f baseMap) residueB)
      (pullback.snd f residueA) residueMap :=
  (IsPullback.of_hasPullback f baseMap).paste_twist_right
    (IsPullback.of_hasPullback f residueA) residueB residueMap
    (residue_square (A := A) (B := B))
    (pullback.fst (pullback.snd f baseMap) residueB)
    (pullback.snd (pullback.snd f baseMap) residueB)
    (IsPullback.of_hasPullback (pullback.snd f baseMap) residueB)
    (closedFiberBaseChangeMap_fst f) (closedFiberBaseChangeMap_snd f)

/-- If the maximal ideal extends to the new maximal ideal, the same closed
fibre is the pullback of the original closed-fibre inclusion over the base. -/
lemma isPullback_closedFiberBaseChangeMap_over_base
    (hMaximal : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    IsPullback (closedFiberBaseChangeMap (B := B) f)
      (pullback.snd (pullback.snd f baseMap) residueB ≫ residueB)
      (pullback.fst f residueA ≫ f) baseMap := by
  have hResidue := isPullback_SpecMap_of_isPushout
    (CommRingCat.ofHom (IsLocalRing.residue A)) (CommRingCat.ofHom (algebraMap A B))
    (CommRingCat.ofHom (IsLocalRing.ResidueField.map (algebraMap A B)))
    (CommRingCat.ofHom (IsLocalRing.residue B))
    (CommRingCat.isPushout_residue_of_maximalIdeal_map_eq A B hMaximal)
  have hPasted := (isPullback_closedFiberBaseChangeMap (B := B) f).paste_vert hResidue
  rw [← pullback.condition (f := f) (g := residueA)] at hPasted
  exact hPasted

/-- The explicit identification with the base change of the closed-fibre inclusion. -/
def closedFiberBaseChangeIso
    (hMaximal : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    pullback (pullback.snd f baseMap) residueB ≅
      pullback (pullback.fst f residueA ≫ f) baseMap :=
  (isPullback_closedFiberBaseChangeMap_over_base (B := B) f hMaximal).isoPullback

/-- Under the explicit comparison, the base change of the old closed-fibre
inclusion is exactly the new closed-fibre inclusion. -/
lemma closedFiberBaseChangeIso_hom_baseChange
    (hMaximal : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B) :
    (closedFiberBaseChangeIso (B := B) f hMaximal).hom ≫
      pullback.map (pullback.fst f residueA ≫ f) baseMap f baseMap
        (pullback.fst f residueA) (𝟙 _) (𝟙 _)
        (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) =
      pullback.fst (pullback.snd f baseMap) residueB := by
  dsimp only [closedFiberBaseChangeIso]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, ← Category.assoc]
    rw [(isPullback_closedFiberBaseChangeMap_over_base (B := B) f hMaximal).isoPullback_hom_fst,
      closedFiberBaseChangeMap_fst]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id]
    rw [(isPullback_closedFiberBaseChangeMap_over_base (B := B) f hMaximal).isoPullback_hom_snd]
    exact (pullback.condition (f := pullback.snd f baseMap) (g := residueB)).symm

end AlgebraicGeometry
