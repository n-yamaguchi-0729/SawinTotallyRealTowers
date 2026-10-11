/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.SchemeTheory.Gluing.CommonCover
import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Recovering relative schemes from common open covers
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Cover

/-- Recovery from common open charts retains the actual structural map to the base. -/
theorem exists_over_iso_of_common_open_cover
    {S : Scheme.{u}} {ι : Type u} (X Y : Over S)
    (A : ι → Over S) (V : ι × ι → Scheme.{u})
    (d : ∀ i j : ι, V (i, j) ⟶ (A i).left)
    (r : ∀ i j : ι, V (i, j) ⟶ (A j).left)
    (a : ∀ i : ι, A i ⟶ X) (b : ∀ i : ι, A i ⟶ Y)
    [∀ i : ι, IsOpenImmersion (a i).left] [∀ i : ι, IsOpenImmersion (b i).left]
    (ha : ∀ x : X.left, ∃ (i : ι) (z : (A i).left), (a i).left z = x)
    (hb : ∀ y : Y.left, ∃ (i : ι) (z : (A i).left), (b i).left z = y)
    (hA : ∀ i j : ι, IsPullback (d i j) (r i j) (a i).left (a j).left)
    (hB : ∀ i j : ι, IsPullback (d i j) (r i j) (b i).left (b j).left) :
    ∃ e : X ≅ Y, ∀ i : ι, a i ≫ e.hom = b i := by
  obtain ⟨e, he⟩ := exists_iso_of_common_open_cover X.left Y.left (fun i ↦ (A i).left)
    V d r (fun i ↦ (a i).left) (fun i ↦ (b i).left) ha hb hA hB
  let 𝒜 : X.left.OpenCover :=
    { I₀ := ι, X := fun i ↦ (A i).left, f := fun i ↦ (a i).left
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨ha, inferInstance⟩ }
  have hw : e.hom ≫ Y.hom = X.hom := by
    apply 𝒜.hom_ext
    intro i
    change (a i).left ≫ (e.hom ≫ Y.hom) = (a i).left ≫ X.hom
    rw [← Category.assoc, he i, Over.w, Over.w]
  refine ⟨Over.isoMk e hw, fun i ↦ ?_⟩
  apply Over.OverMorphism.ext
  exact he i

end AlgebraicGeometry.Scheme.Cover
