/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Transport of recovered charts through an actual natural isomorphism

Changing the base-change functor along a specified natural isomorphism
preserves the recovered open cover, its cartesian structure squares, and
the actual pairwise recovery equations.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Cover

universe u v

variable {S L : Scheme.{u}}
variable {F G : Over S ⥤ Over L} (e : F ≅ G)

/-- Precomposing a recovered chart with the inverse comparison preserves
its open immersion into the recovered scheme. -/
theorem recoveredChartTransport_isOpenImmersion
    {A : Over S} {Z : Over L} (h : F.obj A ⟶ Z) [IsOpenImmersion h.left] :
    IsOpenImmersion ((e.inv.app A ≫ h).left) := by
  let q : (G.obj A).left ≅ (F.obj A).left :=
    (Over.forget L).mapIso ((e.app A).symm)
  change IsOpenImmersion (q.hom ≫ h.left)
  infer_instance

/-- The transported family is an actual open cover, obtained by copying
the original cover along the comparison isomorphisms. -/
def recoveredChartTransportOpenCover
    {K : Type v} (A : K → Over S) (Z : Over L) (h : ∀ i, F.obj (A i) ⟶ Z)
    [∀ i, IsOpenImmersion (h i).left]
    (hcover : ∀ z : Z.left, ∃ (i : K) (x : (F.obj (A i)).left), (h i).left x = z) :
    Z.left.OpenCover := by
  let old : Z.left.OpenCover := Cover.mkOfCovers K (fun i ↦ (F.obj (A i)).left)
    (fun i ↦ (h i).left) hcover (fun i ↦ inferInstanceAs (IsOpenImmersion (h i).left))
  exact Cover.copy old K (fun i ↦ (G.obj (A i)).left)
    (fun i ↦ (e.inv.app (A i) ≫ h i).left) (Equiv.refl K)
    (fun i ↦ (Over.forget L).mapIso ((e.app (A i)).symm)) (fun i ↦ rfl)

/-- Every point is still in a transported chart. -/
theorem recoveredChartTransport_covers
    {K : Type v} (A : K → Over S) (Z : Over L) (h : ∀ i, F.obj (A i) ⟶ Z)
    [∀ i, IsOpenImmersion (h i).left]
    (hcover : ∀ z : Z.left, ∃ (i : K) (x : (F.obj (A i)).left), (h i).left x = z)
    (z : Z.left) :
    ∃ (i : K) (x : (G.obj (A i)).left), (e.inv.app (A i) ≫ h i).left x = z :=
  (recoveredChartTransportOpenCover e A Z h hcover).exists_eq z

/-- A recovered structural pullback square remains cartesian after
transporting the base-change functor through the actual comparison. -/
theorem recoveredChartTransport_isPullback
    {A U : Over S} {Z : Over L} (y : A ⟶ U) (h : F.obj A ⟶ Z)
    (hPB : IsPullback (F.map y).left h.left (F.obj U).hom Z.hom) :
    IsPullback (G.map y).left (e.inv.app A ≫ h).left (G.obj U).hom Z.hom := by
  let eA : (F.obj A).left ≅ (G.obj A).left := (Over.forget L).mapIso (e.app A)
  let eU : (F.obj U).left ≅ (G.obj U).left := (Over.forget L).mapIso (e.app U)
  apply hPB.of_iso eA eU (Iso.refl Z.left) (Iso.refl L)
  · exact congrArg (fun t : F.obj A ⟶ G.obj U ↦ t.left) (e.hom.naturality y)
  · exact (Category.comp_id h.left).trans (eA.hom_inv_id_assoc h.left).symm
  · exact (Category.comp_id (F.obj U).hom).trans (Over.w (e.hom.app U)).symm
  · exact (Category.comp_id Z.hom).trans (Category.id_comp Z.hom).symm

/-- The pairwise recovered-chart equation is preserved by compatible
transport of the overlap morphism.  All maps are the original maps over
the two bases; no faithfulness assumption is used. -/
theorem recoveredChartTransport_pair
    {A B V W : Over S} {Z : Over L}
    (d : V ⟶ A) (r : W ⟶ B) (hA : F.obj A ⟶ Z) (hB : F.obj B ⟶ Z)
    (a : F.obj V ⟶ F.obj W) (b : G.obj V ⟶ G.obj W)
    (hab : e.hom.app V ≫ b = a ≫ e.hom.app W)
    (hrec : a ≫ F.map r ≫ hB = F.map d ≫ hA) :
    b ≫ G.map r ≫ (e.inv.app B ≫ hB) = G.map d ≫ (e.inv.app A ≫ hA) := by
  let eA : F.obj A ≅ G.obj A := e.app A
  let eB : F.obj B ≅ G.obj B := e.app B
  let eV : F.obj V ≅ G.obj V := e.app V
  let eW : F.obj W ≅ G.obj W := e.app W
  have hd : F.map d ≫ eA.hom = eV.hom ≫ G.map d := e.hom.naturality d
  have hr : F.map r ≫ eB.hom = eW.hom ≫ G.map r := e.hom.naturality r
  have hd' : eV.hom ≫ G.map d ≫ eA.inv = F.map d := by
    rw [← Category.assoc, ← hd, Category.assoc, eA.hom_inv_id, Category.comp_id]
  have hr' : eW.hom ≫ G.map r ≫ eB.inv = F.map r := by
    rw [← Category.assoc, ← hr, Category.assoc, eB.hom_inv_id, Category.comp_id]
  change b ≫ G.map r ≫ (eB.inv ≫ hB) = G.map d ≫ (eA.inv ≫ hA)
  apply (cancel_epi eV.hom).1
  calc
    eV.hom ≫ (b ≫ G.map r ≫ (eB.inv ≫ hB)) =
        (eV.hom ≫ b) ≫ (G.map r ≫ (eB.inv ≫ hB)) := (Category.assoc _ _ _).symm
    _ = (a ≫ eW.hom) ≫ (G.map r ≫ (eB.inv ≫ hB)) :=
      congrArg (fun q ↦ q ≫ (G.map r ≫ (eB.inv ≫ hB))) hab
    _ = a ≫ ((eW.hom ≫ G.map r ≫ eB.inv) ≫ hB) := by simp only [Category.assoc]
    _ = a ≫ (F.map r ≫ hB) := congrArg (fun q ↦ a ≫ (q ≫ hB)) hr'
    _ = F.map d ≫ hA := hrec
    _ = (eV.hom ≫ G.map d ≫ eA.inv) ≫ hA := congrArg (fun q ↦ q ≫ hA) hd'.symm
    _ = eV.hom ≫ (G.map d ≫ (eA.inv ≫ hA)) := by simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Cover
