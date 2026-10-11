/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RecoveredChartTransport
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Transport of actual recovered overlap squares

The actual overlap isomorphism and its compatibility with the functor
comparison transport both projections of the recovered cartesian square.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Cover

universe u

/-- A recovered overlap square remains cartesian after transporting the
base-change functor and its actual overlap morphism. -/
theorem recoveredOverlapTransport_isPullback
    {S L : Scheme.{u}} {F G : Over S ⥤ Over L} (e : F ≅ G)
    {A B V W : Over S} {Z : Over L}
    (d : V ⟶ A) (r : W ⟶ B) (hA : F.obj A ⟶ Z) (hB : F.obj B ⟶ Z)
    (a : F.obj V ⟶ F.obj W) (b : G.obj V ⟶ G.obj W)
    (hab : e.hom.app V ≫ b = a ≫ e.hom.app W)
    (hPB : IsPullback (F.map d).left (a ≫ F.map r).left hA.left hB.left) :
    IsPullback (G.map d).left (b ≫ G.map r).left
      (e.inv.app A ≫ hA).left (e.inv.app B ≫ hB).left := by
  let eV : (F.obj V).left ≅ (G.obj V).left := (Over.forget L).mapIso (e.app V)
  let eA : (F.obj A).left ≅ (G.obj A).left := (Over.forget L).mapIso (e.app A)
  let eB : (F.obj B).left ≅ (G.obj B).left := (Over.forget L).mapIso (e.app B)
  have hr : (a ≫ F.map r) ≫ e.hom.app B = e.hom.app V ≫ (b ≫ G.map r) := by
    calc
      (a ≫ F.map r) ≫ e.hom.app B = a ≫ (F.map r ≫ e.hom.app B) :=
        Category.assoc _ _ _
      _ = a ≫ (e.hom.app W ≫ G.map r) :=
        congrArg (fun q ↦ a ≫ q) (e.hom.naturality r)
      _ = (a ≫ e.hom.app W) ≫ G.map r := (Category.assoc _ _ _).symm
      _ = (e.hom.app V ≫ b) ≫ G.map r := congrArg (fun q ↦ q ≫ G.map r) hab.symm
      _ = e.hom.app V ≫ (b ≫ G.map r) := Category.assoc _ _ _
  apply hPB.of_iso eV eA eB (Iso.refl Z.left)
  · exact congrArg (fun q : F.obj V ⟶ G.obj A ↦ q.left) (e.hom.naturality d)
  · exact congrArg (fun q : F.obj V ⟶ G.obj B ↦ q.left) hr
  · exact (Category.comp_id hA.left).trans (eA.hom_inv_id_assoc hA.left).symm
  · exact (Category.comp_id hB.left).trans (eB.hom_inv_id_assoc hB.left).symm

end AlgebraicGeometry.Scheme.Cover
