/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Open covers under coefficient pullback
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Cover

/-- The actual map produced by coefficient pullback has its canonical cartesian square. -/
theorem overCoefficientPullback_isPullback
    {B B' : Scheme.{u}} (ψ : B' ⟶ B) {A C : Over B} (m : A ⟶ C) :
    IsPullback ((Over.pullback ψ).map m).left (pullback.fst A.hom ψ)
      (pullback.fst C.hom ψ) m.left := by
  refine IsPullback.of_right ?_ ?_ (IsPullback.of_hasPullback C.hom ψ).flip
  · have h₁ : ((Over.pullback ψ).map m).left ≫ pullback.snd C.hom ψ =
        pullback.snd A.hom ψ := ((Over.pullback ψ).map m).w
    have h₂ : m.left ≫ C.hom = A.hom := m.w
    rw [h₁, h₂]
    exact (IsPullback.of_hasPullback A.hom ψ).flip
  · exact pullback.lift_fst _ _ _

/-- A cartesian square of schemes over the coefficient base remains cartesian
under the actual coefficient-pullback functor. -/
theorem overCoefficientPullback_map_isPullback
    {B B' : Scheme.{u}} (ψ : B' ⟶ B) {P A C Y : Over B}
    (d : P ⟶ A) (r : P ⟶ C) (a : A ⟶ Y) (c : C ⟶ Y)
    (h : IsPullback d.left r.left a.left c.left) :
    IsPullback ((Over.pullback ψ).map d).left ((Over.pullback ψ).map r).left
      ((Over.pullback ψ).map a).left ((Over.pullback ψ).map c).left := by
  have hO : IsPullback d r a c :=
    IsPullback.of_map_of_faithful (Over.forget B) h
  exact hO.map (Over.pullback ψ ⋙ Over.forget B')

/-- An actual open cover over the coefficient base remains an open cover after
pullback, with precisely the objects and maps of `Over.pullback`. -/
def overCoefficientPullbackCover
    {B B' : Scheme.{u}} (ψ : B' ⟶ B) {ι : Type u}
    (Y : Over B) (A : ι → Over B) (m : ∀ i : ι, A i ⟶ Y)
    [∀ i : ι, IsOpenImmersion (m i).left]
    (hc : ∀ y : Y.left, ∃ (i : ι) (a : (A i).left), (m i).left a = y) :
    ((Over.pullback ψ).obj Y).left.OpenCover := by
  let 𝒰 : Y.left.OpenCover :=
    { I₀ := ι, X i := (A i).left, f i := (m i).left
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hc, inferInstance⟩ }
  refine Scheme.Cover.copy (𝒰.pullback₁ (pullback.fst Y.hom ψ)) ι
    (fun i ↦ ((Over.pullback ψ).obj (A i)).left)
    (fun i ↦ ((Over.pullback ψ).map (m i)).left)
    (Equiv.refl _) (fun i ↦ (overCoefficientPullback_isPullback ψ (m i)).isoPullback) ?_
  intro i
  exact (overCoefficientPullback_isPullback ψ (m i)).isoPullback_hom_fst.symm

end AlgebraicGeometry.Scheme.Cover
