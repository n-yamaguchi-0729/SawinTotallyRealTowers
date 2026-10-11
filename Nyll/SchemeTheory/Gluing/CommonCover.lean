/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Recovering schemes from common open covers
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Cover

/-- Two schemes covered by the same charts with the same actual overlaps
are isomorphic, with the isomorphism respecting each chart map. -/
theorem exists_iso_of_common_open_cover
    {ι : Type u} (X Y : Scheme.{u}) (A : ι → Scheme.{u}) (V : ι × ι → Scheme.{u})
    (d : ∀ i j : ι, V (i, j) ⟶ A i) (r : ∀ i j : ι, V (i, j) ⟶ A j)
    (a : ∀ i : ι, A i ⟶ X) (b : ∀ i : ι, A i ⟶ Y)
    [∀ i : ι, IsOpenImmersion (a i)] [∀ i : ι, IsOpenImmersion (b i)]
    (ha : ∀ x : X, ∃ (i : ι) (z : A i), a i z = x)
    (hb : ∀ y : Y, ∃ (i : ι) (z : A i), b i z = y)
    (hA : ∀ i j : ι, IsPullback (d i j) (r i j) (a i) (a j))
    (hB : ∀ i j : ι, IsPullback (d i j) (r i j) (b i) (b j)) :
    ∃ e : X ≅ Y, ∀ i : ι, a i ≫ e.hom = b i := by
  let 𝒜 : X.OpenCover :=
    { I₀ := ι, X := A, f := a
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨ha, inferInstance⟩ }
  let ℬ : Y.OpenCover :=
    { I₀ := ι, X := A, f := b
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hb, inferInstance⟩ }
  have hab (i j : ι) : pullback.fst (a i) (a j) ≫ b i =
      pullback.snd (a i) (a j) ≫ b j := by
    rw [← (hA i j).isoPullback_inv_fst, ← (hA i j).isoPullback_inv_snd,
      Category.assoc, Category.assoc, (hB i j).w]
  have hba (i j : ι) : pullback.fst (b i) (b j) ≫ a i =
      pullback.snd (b i) (b j) ≫ a j := by
    rw [← (hB i j).isoPullback_inv_fst, ← (hB i j).isoPullback_inv_snd,
      Category.assoc, Category.assoc, (hA i j).w]
  let g : X ⟶ Y := 𝒜.glueMorphisms b hab
  let h : Y ⟶ X := ℬ.glueMorphisms a hba
  have hg (i : ι) : a i ≫ g = b i := 𝒜.ι_glueMorphisms b hab i
  have hh (i : ι) : b i ≫ h = a i := ℬ.ι_glueMorphisms a hba i
  have hgh : g ≫ h = 𝟙 X := by
    apply 𝒜.hom_ext
    intro i
    change a i ≫ (g ≫ h) = a i ≫ 𝟙 X
    rw [← Category.assoc, hg, hh, Category.comp_id]
  have hhg : h ≫ g = 𝟙 Y := by
    apply ℬ.hom_ext
    intro i
    change b i ≫ (h ≫ g) = b i ≫ 𝟙 Y
    rw [← Category.assoc, hh, hg, Category.comp_id]
  exact ⟨⟨g, h, hgh, hhg⟩, hg⟩

/-- A cartesian overlap over the base is the overlap of two cartesian charts. -/
theorem isPullback_of_cartesian_chart_overlap
    {A C V U W X S : Scheme.{u}}
    (a : A ⟶ X) (c : C ⟶ X) (f : X ⟶ S)
    (y : A ⟶ U) (z : C ⟶ W) (u : U ⟶ S) (w : W ⟶ S)
    (d : V ⟶ A) (r : V ⟶ C) (ℓ : V ⟶ W)
    (ha : y ≫ u = a ≫ f) (hc : IsPullback z c w f)
    (hV : IsPullback d ℓ (y ≫ u) w)
    (hr : r ≫ z = ℓ) (hcompat : d ≫ a = r ≫ c) :
    IsPullback d r a c := by
  have houter : IsPullback (r ≫ z) d w (a ≫ f) := by
    rw [hr, ← ha]
    exact hV.flip
  exact (IsPullback.of_right houter hcompat.symm hc).flip

end AlgebraicGeometry.Scheme.Cover
