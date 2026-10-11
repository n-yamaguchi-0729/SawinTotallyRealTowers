/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Yoneda

/-!
# Canonical transitions between local representing objects

Restrict a presheaf on `C` to the slice over each object of `C`. Given
representing objects on two slices, a morphism between the bases determines
a canonical morphism between the representing objects. The universal
elements make these transitions compatible with identities and composition.

If `C` has pullbacks, the transition square is a pullback. These constructions
apply to `C = Over S`; the iterated slice equivalence then identifies the
local restrictions with the usual presheaves on schemes over each local base.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

noncomputable section

namespace SchemeTheory.WeilRestriction

variable {C : Type u} [Category.{v} C]

/-- Restrict a presheaf to the slice over an object of its domain. -/
abbrev sliceRestriction (F : Cᵒᵖ ⥤ Type w) (U : C) : (Over U)ᵒᵖ ⥤ Type w :=
  (Over.forget U).op ⋙ F

variable {F : Cᵒᵖ ⥤ Type w} {U V Z : C}
  {WU : Over U} {WV : Over V} {WZ : Over Z}

/-- The canonical transition between local representers as a morphism over the target base. -/
def localRepresenterOverMap
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    (Over.map a).obj WU ⟶ WV :=
  (hV.homEquiv (X := (Over.map a).obj WU)).symm (hU.homEquiv (𝟙 WU))

/-- The canonical transition sends the universal element on the target
to the universal element on the source. -/
def localRepresenterMap
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    WU.left ⟶ WV.left :=
  (localRepresenterOverMap hU hV a).left

/-- The transition commutes with the structure morphisms. -/
lemma localRepresenterMap_w
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    localRepresenterMap hU hV a ≫ WV.hom = WU.hom ≫ a :=
  Over.w (localRepresenterOverMap hU hV a)

/-- The defining compatibility between universal elements. -/
lemma localRepresenterMap_universal
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    F.map (localRepresenterMap hU hV a).op (hV.homEquiv (𝟙 WV)) =
      hU.homEquiv (𝟙 WU) :=
  (hV.homEquiv_eq (localRepresenterOverMap hU hV a)).symm.trans
    ((hV.homEquiv (X := (Over.map a).obj WU)).apply_symm_apply
      (hU.homEquiv (𝟙 WU)))

/-- A transition is uniquely determined by its base map and universal element. -/
lemma localRepresenterMap_unique
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V)
    (g : WU.left ⟶ WV.left) (hg : g ≫ WV.hom = WU.hom ≫ a)
    (hF : F.map g.op (hV.homEquiv (𝟙 WV)) = hU.homEquiv (𝟙 WU)) :
    g = localRepresenterMap hU hV a := by
  have h : (Over.homMk g hg : (Over.map a).obj WU ⟶ WV) =
      localRepresenterOverMap hU hV a := by
    apply hV.homEquiv.injective
    exact (hV.homEquiv_eq
      (Over.homMk g hg : (Over.map a).obj WU ⟶ WV)).trans <|
      hF.trans ((hV.homEquiv (X := (Over.map a).obj WU)).apply_symm_apply
        (hU.homEquiv (𝟙 WU))).symm
  exact congrArg (fun k : (Over.map a).obj WU ⟶ WV => k.left) h

/-- Canonical transitions preserve identity morphisms. -/
lemma localRepresenterMap_id
    (hU : (sliceRestriction F U).RepresentableBy WU) :
    localRepresenterMap hU hU (𝟙 U) = 𝟙 WU.left := by
  symm
  apply localRepresenterMap_unique hU hU (𝟙 U) (𝟙 WU.left)
  · rw [Category.id_comp, Category.comp_id]
  · change F.map (𝟙 (Opposite.op WU.left)) (hU.homEquiv (𝟙 WU)) =
      hU.homEquiv (𝟙 WU)
    rw [F.map_id]
    rfl

/-- Canonical transitions preserve composition. -/
lemma localRepresenterMap_comp
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV)
    (hZ : (sliceRestriction F Z).RepresentableBy WZ)
    (a : U ⟶ V) (b : V ⟶ Z) :
    localRepresenterMap hU hZ (a ≫ b) =
      localRepresenterMap hU hV a ≫ localRepresenterMap hV hZ b := by
  symm
  apply localRepresenterMap_unique hU hZ (a ≫ b)
    (localRepresenterMap hU hV a ≫ localRepresenterMap hV hZ b)
  · rw [Category.assoc, localRepresenterMap_w, ← Category.assoc,
      localRepresenterMap_w, Category.assoc]
  · change F.map
      ((localRepresenterMap hV hZ b).op ≫ (localRepresenterMap hU hV a).op)
      (hZ.homEquiv (𝟙 WZ)) = hU.homEquiv (𝟙 WU)
    rw [F.map_comp]
    change F.map (localRepresenterMap hU hV a).op
      (F.map (localRepresenterMap hV hZ b).op (hZ.homEquiv (𝟙 WZ))) =
        hU.homEquiv (𝟙 WU)
    rw [localRepresenterMap_universal, localRepresenterMap_universal]

section Pullback

variable [HasPullbacks C]

/-- Restriction of a locally represented presheaf along a base morphism is
represented by the pullback, via the map-pullback adjunction. -/
def localRepresenterPullbackRepresentable
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    (sliceRestriction F U).RepresentableBy ((Over.pullback a).obj WV) where
  homEquiv {X} := ((Over.mapPullbackAdj a).homEquiv X WV).symm.trans hV.homEquiv
  homEquiv_comp {X X'} f g := by
    change hV.homEquiv
      (((Over.mapPullbackAdj a).homEquiv X WV).symm (f ≫ g)) = _
    rw [Adjunction.homEquiv_naturality_left_symm]
    exact hV.homEquiv_comp ((Over.map a).map f)
      (((Over.mapPullbackAdj a).homEquiv X' WV).symm g)

/-- The canonical comparison with the pullback of a local representer. -/
def localRepresenterPullbackIso
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    WU ≅ (Over.pullback a).obj WV :=
  hU.uniqueUpToIso (localRepresenterPullbackRepresentable hV a)

private lemma localRepresenterPullbackIso_homEquiv
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    (localRepresenterPullbackRepresentable hV a).homEquiv
      (localRepresenterPullbackIso hU hV a).hom = hU.homEquiv (𝟙 WU) := by
  change (localRepresenterPullbackRepresentable hV a).homEquiv
    ((localRepresenterPullbackRepresentable hV a).homEquiv.symm
      (hU.homEquiv (𝟙 WU))) = hU.homEquiv (𝟙 WU)
  exact (localRepresenterPullbackRepresentable hV a).homEquiv.apply_symm_apply _

/-- The pullback comparison recovers the canonical transition after projection. -/
lemma localRepresenterPullbackIso_hom_fst
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    (localRepresenterPullbackIso hU hV a).hom.left ≫ pullback.fst WV.hom a =
      localRepresenterMap hU hV a := by
  have h : ((Over.mapPullbackAdj a).homEquiv WU WV).symm
      (localRepresenterPullbackIso hU hV a).hom =
        localRepresenterOverMap hU hV a := by
    apply hV.homEquiv.injective
    exact (localRepresenterPullbackIso_homEquiv hU hV a).trans
      ((hV.homEquiv (X := (Over.map a).obj WU)).apply_symm_apply
        (hU.homEquiv (𝟙 WU))).symm
  have hleft := congrArg (fun k : (Over.map a).obj WU ⟶ WV => k.left) h
  change (localRepresenterPullbackIso hU hV a).hom.left ≫
    (𝟙 (pullback WV.hom a) ≫ pullback.fst WV.hom a) =
      localRepresenterMap hU hV a at hleft
  simpa [Over.mapPullbackAdj] using hleft

/-- Canonical transitions give cartesian squares over their base morphisms. -/
lemma localRepresenterMap_isPullback
    (hU : (sliceRestriction F U).RepresentableBy WU)
    (hV : (sliceRestriction F V).RepresentableBy WV) (a : U ⟶ V) :
    IsPullback (localRepresenterMap hU hV a) WU.hom WV.hom a := by
  refine IsPullback.of_iso_pullback ⟨localRepresenterMap_w hU hV a⟩
    ((Over.forget U).mapIso (localRepresenterPullbackIso hU hV a)) ?_ ?_
  · exact localRepresenterPullbackIso_hom_fst hU hV a
  · exact Over.w (localRepresenterPullbackIso hU hV a).hom

end Pullback

end SchemeTheory.WeilRestriction
