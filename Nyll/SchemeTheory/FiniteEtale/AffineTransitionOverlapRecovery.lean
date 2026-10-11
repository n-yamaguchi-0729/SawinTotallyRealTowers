/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.AffineTransitionLocalModel
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Actual overlap comparisons from recovered local models

Restrict a recovered local model to any smaller base open. The literal
inclusions commute with the restricted cone maps, so native pullback
composition transports its given recovery to the restriction of the same
original cover. On an overlap the two resulting recovery isomorphisms have
the identical target, and their composition supplies the overlap isomorphism.

The only model data here are the local models and their already constructed
recoveries to the original cover. No overlap comparison is an input.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleOverCategoryOverlapRecovery (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongOverlapRecovery
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongOverlapRecovery
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)

/-- The literal inclusion between two stage preimages of nested opens. -/
def openStageInclusion (i : I) (U V : (D.obj i).Opens) (h : V ≤ U) (t : Over i) :
    (D.map t.hom ⁻¹ᵁ V).toScheme ⟶ (D.map t.hom ⁻¹ᵁ U).toScheme :=
  (D.obj t.left).homOfLE ((D.map t.hom).preimage_mono h)

/-- The literal inclusion between two cone preimages of nested opens. -/
def openLimitInclusion (i : I) (U V : (D.obj i).Opens) (h : V ≤ U) :
    (c.π.app i ⁻¹ᵁ V).toScheme ⟶ (c.π.app i ⁻¹ᵁ U).toScheme :=
  c.pt.homOfLE ((c.π.app i).preimage_mono h)

/-- Stage and limit inclusions commute with the actual restricted cone maps. -/
theorem openInclusion_cone_map
    (i : I) (U V : (D.obj i).Opens) (h : V ≤ U) (t : Over i) :
    (opensCone D c i V).π.app t ≫ openStageInclusion D i U V h t =
      openLimitInclusion D c i U V h ≫ (opensCone D c i U).π.app t := by
  let pU : (c.π.app i ⁻¹ᵁ U).toScheme ⟶ (D.map t.hom ⁻¹ᵁ U).toScheme :=
    (opensCone D c i U).π.app t
  let pV : (c.π.app i ⁻¹ᵁ V).toScheme ⟶ (D.map t.hom ⁻¹ᵁ V).toScheme :=
    (opensCone D c i V).π.app t
  let a : (D.map t.hom ⁻¹ᵁ V).toScheme ⟶ (D.map t.hom ⁻¹ᵁ U).toScheme :=
    openStageInclusion D i U V h t
  let b : (c.π.app i ⁻¹ᵁ V).toScheme ⟶ (c.π.app i ⁻¹ᵁ U).toScheme :=
    openLimitInclusion D c i U V h
  have hU : pU ≫ (D.map t.hom ⁻¹ᵁ U).ι =
      (c.π.app i ⁻¹ᵁ U).ι ≫ c.π.app t.left :=
    (opensCone_isPullback D c i U t).w
  have hV : pV ≫ (D.map t.hom ⁻¹ᵁ V).ι =
      (c.π.app i ⁻¹ᵁ V).ι ≫ c.π.app t.left :=
    (opensCone_isPullback D c i V t).w
  have ha : a ≫ (D.map t.hom ⁻¹ᵁ U).ι = (D.map t.hom ⁻¹ᵁ V).ι :=
    Scheme.homOfLE_ι (D.obj t.left) ((D.map t.hom).preimage_mono h)
  have hb : b ≫ (c.π.app i ⁻¹ᵁ U).ι = (c.π.app i ⁻¹ᵁ V).ι :=
    Scheme.homOfLE_ι c.pt ((c.π.app i).preimage_mono h)
  change pV ≫ a = b ≫ pU
  apply (cancel_mono (D.map t.hom ⁻¹ᵁ U).ι).mp
  rw [Category.assoc, ha, hV, Category.assoc, hU, ← Category.assoc, hb]

/-- Restricting a recovered local model recovers the restriction of the same
original finite-etale cover, through the literal native pullback comparisons. -/
def recoveredRestrictionIso
    (i : I) (U V : (D.obj i).Opens) (h : V ≤ U) (t : Over i)
    (X : FiniteEtale c.pt) (M : FiniteEtale ((opensDiagram D i U).obj t))
    (e : (FiniteEtale.pullback ((opensCone D c i U).π.app t)).obj M ≅
      (FiniteEtale.pullback (c.π.app i ⁻¹ᵁ U).ι).obj X) :
    (FiniteEtale.pullback ((opensCone D c i V).π.app t)).obj
        ((FiniteEtale.pullback (openStageInclusion D i U V h t)).obj M) ≅
      (FiniteEtale.pullback (c.π.app i ⁻¹ᵁ V).ι).obj X := by
  let pU : (c.π.app i ⁻¹ᵁ U).toScheme ⟶ (D.map t.hom ⁻¹ᵁ U).toScheme :=
    (opensCone D c i U).π.app t
  let pV : (c.π.app i ⁻¹ᵁ V).toScheme ⟶ (D.map t.hom ⁻¹ᵁ V).toScheme :=
    (opensCone D c i V).π.app t
  let a := openStageInclusion D i U V h t
  let b := openLimitInclusion D c i U V h
  let iU : (c.π.app i ⁻¹ᵁ U).toScheme ⟶ c.pt := (c.π.app i ⁻¹ᵁ U).ι
  let iV : (c.π.app i ⁻¹ᵁ V).toScheme ⟶ c.pt := (c.π.app i ⁻¹ᵁ V).ι
  have hsquare : pV ≫ a = b ≫ pU := openInclusion_cone_map D c i U V h t
  have hi : b ≫ iU = iV := Scheme.homOfLE_ι c.pt ((c.π.app i).preimage_mono h)
  let q₁ : FiniteEtale.pullback (pV ≫ a) ≅
      FiniteEtale.pullback a ⋙ FiniteEtale.pullback pV :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) pV a
  let q₂ : FiniteEtale.pullback (pV ≫ a) ≅ FiniteEtale.pullback (b ≫ pU) :=
    MorphismProperty.Over.pullbackCongr
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) hsquare
  let q₃ : FiniteEtale.pullback (b ≫ pU) ≅
      FiniteEtale.pullback pU ⋙ FiniteEtale.pullback b :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) b pU
  let q₄ : FiniteEtale.pullback (b ≫ iU) ≅
      FiniteEtale.pullback iU ⋙ FiniteEtale.pullback b :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) b iU
  let q₅ : FiniteEtale.pullback (b ≫ iU) ≅ FiniteEtale.pullback iV :=
    MorphismProperty.Over.pullbackCongr
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) hi
  exact (q₁.app M).symm ≪≫ q₂.app M ≪≫ q₃.app M ≪≫
    (FiniteEtale.pullback b).mapIso e ≪≫ (q₄.app X).symm ≪≫ q₅.app X

/-- The actual limit-overlap isomorphism between two recovered stage models.
Its two recovery maps land in the identical restriction of the original `X`. -/
def recoveredOverlapIso
    (i : I) (U V : (D.obj i).Opens) (t : Over i) (X : FiniteEtale c.pt)
    (M : FiniteEtale ((opensDiagram D i U).obj t))
    (N : FiniteEtale ((opensDiagram D i V).obj t))
    (eM : (FiniteEtale.pullback ((opensCone D c i U).π.app t)).obj M ≅
      (FiniteEtale.pullback (c.π.app i ⁻¹ᵁ U).ι).obj X)
    (eN : (FiniteEtale.pullback ((opensCone D c i V).π.app t)).obj N ≅
      (FiniteEtale.pullback (c.π.app i ⁻¹ᵁ V).ι).obj X) :
    (FiniteEtale.pullback ((opensCone D c i (U ⊓ V)).π.app t)).obj
        ((FiniteEtale.pullback (openStageInclusion D i U (U ⊓ V) inf_le_left t)).obj M) ≅
      (FiniteEtale.pullback ((opensCone D c i (U ⊓ V)).π.app t)).obj
        ((FiniteEtale.pullback (openStageInclusion D i V (U ⊓ V) inf_le_right t)).obj N) :=
  recoveredRestrictionIso D c i U (U ⊓ V) inf_le_left t X M eM ≪≫
    (recoveredRestrictionIso D c i V (U ⊓ V) inf_le_right t X N eN).symm

end AlgebraicGeometry.FiniteEtale
