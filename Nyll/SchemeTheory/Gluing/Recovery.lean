/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Recovering a scheme from actual gluing overlaps

Local comparison maps that cover the target and identify pairwise overlaps
produce the comparison isomorphism from the glued scheme.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.GlueData

/-- Actual local comparison maps whose pairwise overlaps are the gluing overlaps
construct an isomorphism from the glued scheme to the scheme they cover. -/
theorem exists_glueData_iso_of_overlap
    (D : Scheme.GlueData.{u}) (Z : Scheme.{u})
    (q : ∀ i, D.U i ⟶ Z) [∀ i, IsOpenImmersion (q i)]
    (hcover : ∀ z : Z, ∃ (i : D.J) (x : D.U i), q i x = z)
    (hV : ∀ i j, IsPullback (D.f i j) (D.t i j ≫ D.f j i) (q i) (q j)) :
    ∃ e : D.glued ≅ Z, ∀ i, D.ι i ≫ e.hom = q i := by
  have hcompat (a : D.J × D.J) :
      D.diagram.fst a ≫ q a.1 = D.diagram.snd a ≫ q a.2 :=
    (hV a.1 a.2).w
  let toZ : D.glued ⟶ Z := Multicoequalizer.desc D.diagram Z q hcompat
  have htoZ (i : D.J) : D.ι i ≫ toZ = q i :=
    Multicoequalizer.π_desc D.diagram Z q hcompat i
  let 𝒰 : Z.OpenCover :=
    { I₀ := D.J
      X := D.U
      f := q
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hcover, inferInstance⟩ }
  have hinvCompat (i j : D.J) :
      Limits.pullback.fst (q i) (q j) ≫ D.ι i =
        Limits.pullback.snd (q i) (q j) ≫ D.ι j := by
    rw [← (hV i j).isoPullback_inv_fst, ← (hV i j).isoPullback_inv_snd,
      Category.assoc, Category.assoc, Category.assoc, D.glue_condition]
  let fromZ : Z ⟶ D.glued := 𝒰.glueMorphisms D.ι hinvCompat
  have hfromZ (i : D.J) : q i ≫ fromZ = D.ι i :=
    𝒰.ι_glueMorphisms D.ι hinvCompat i
  have hforward : toZ ≫ fromZ = 𝟙 D.glued := by
    apply D.openCover.hom_ext
    change ∀ i : D.J, D.ι i ≫ (toZ ≫ fromZ) = D.ι i ≫ 𝟙 D.glued
    intro i
    rw [← Category.assoc, htoZ, hfromZ, Category.comp_id]
  have hbackward : fromZ ≫ toZ = 𝟙 Z := by
    apply 𝒰.hom_ext
    change ∀ i : D.J, q i ≫ (fromZ ≫ toZ) = q i ≫ 𝟙 Z
    intro i
    rw [← Category.assoc, hfromZ, htoZ, Category.comp_id]
  exact ⟨⟨toZ, fromZ, hforward, hbackward⟩, htoZ⟩

end AlgebraicGeometry.Scheme.GlueData
