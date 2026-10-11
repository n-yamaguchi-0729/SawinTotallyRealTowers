/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHomFamily
import Nyll.SchemeTheory.Descent.AffineTransitionOverComparison

/-!
# Actual native over-category morphism families at a common stage

The real qcqs/LFP scheme Hom supplier is transported through pullback symmetry.
Recovery uses the native cone comparison, with both projection equations
proved from the chosen pullbacks. This applies to raw gluing overlaps over
the ambient base without claiming that those overlaps are finite there.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

private theorem overTransition_eq_symmetry
    {I : Type u} [Category.{u} I] {S : Scheme.{u}}
    (D : I ⥤ Over S) (c : Cone D) (A : Over S) (i : I) :
    overInverseLimitTransition D c A i =
      (pullbackSymmetry c.pt.hom A.hom).inv ≫ (cone D c A.hom).π.app i ≫
        (pullbackSymmetry (D.obj i).hom A.hom).hom := by
  apply pullback.hom_ext
  · rw [overInverseLimitTransition_fst, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_fst, cone_map_snd, pullbackSymmetry_inv_comp_snd]
  · rw [overInverseLimitTransition_snd, Category.assoc, Category.assoc,
      pullbackSymmetry_hom_comp_snd, cone_map_fst,
      ← Category.assoc, pullbackSymmetry_inv_comp_fst]

/-- Finitely many native `Over` morphisms descend to one coefficient stage,
retaining the exact native pullback-comparison recovery equations. -/
theorem exists_over_hom_stage_family
    {I : Type u} [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}}
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    {K : Type v} [Finite K] (A B : K → Over S)
    [∀ k : K, QuasiCompact (A k).hom] [∀ k : K, QuasiSeparated (A k).hom]
    [∀ k : K, LocallyOfFinitePresentation (B k).hom]
    (a : ∀ k : K, (Over.pullback c.pt.hom).obj (A k) ⟶
      (Over.pullback c.pt.hom).obj (B k)) :
    ∃ (i : I) (b : ∀ k : K, (Over.pullback (D.obj i).hom).obj (A k) ⟶
      (Over.pullback (D.obj i).hom).obj (B k)), ∀ k : K,
        (overInverseLimitPullbackComparison D c i).hom.app (A k) ≫
            (Over.pullback (c.π.app i).left).map (b k) =
          a k ≫ (overInverseLimitPullbackComparison D c i).hom.app (B k) := by
  let Y (k : K) : Scheme.{u} := (A k).left
  let Z (k : K) : Scheme.{u} := (B k).left
  let f (k : K) : Y k ⟶ S := (A k).hom
  let g (k : K) : Z k ⟶ S := (B k).hom
  let a₀ (k : K) : pullback (f k) c.pt.hom ⟶ pullback (g k) c.pt.hom := (a k).left
  have ha₀ (k : K) : a₀ k ≫ pullback.snd (g k) c.pt.hom = pullback.snd (f k) c.pt.hom :=
    Over.w (a k)
  let ar (k : K) : pullback c.pt.hom (f k) ⟶ pullback c.pt.hom (g k) :=
    (pullbackSymmetry c.pt.hom (f k)).hom ≫ a₀ k ≫
      (pullbackSymmetry c.pt.hom (g k)).inv
  have har (k : K) : ar k ≫ pullback.fst c.pt.hom (g k) = pullback.fst c.pt.hom (f k) := by
    dsimp only [ar]
    simp only [Category.assoc, pullbackSymmetry_inv_comp_fst, ha₀,
      pullbackSymmetry_hom_comp_snd]
  obtain ⟨i, br, hbr⟩ := exists_hom_stage_family D c hc Y Z f g ar har
  let b₀ (k : K) : pullback (f k) (D.obj i).hom ⟶ pullback (g k) (D.obj i).hom :=
    (pullbackSymmetry (D.obj i).hom (f k)).inv ≫ br k ≫
      (pullbackSymmetry (D.obj i).hom (g k)).hom
  have hb₀ (k : K) : b₀ k ≫ pullback.snd (g k) (D.obj i).hom =
      pullback.snd (f k) (D.obj i).hom := by
    dsimp only [b₀]
    simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, (hbr k).1,
      pullbackSymmetry_inv_comp_fst]
  let b (k : K) : (Over.pullback (D.obj i).hom).obj (A k) ⟶
      (Over.pullback (D.obj i).hom).obj (B k) := Over.homMk (b₀ k) (hb₀ k)
  have hrec (k : K) : overInverseLimitTransition D c (A k) i ≫ b₀ k =
      a₀ k ≫ overInverseLimitTransition D c (B k) i := by
    have H := congrArg (fun z : pullback c.pt.hom (f k) ⟶ pullback (D.obj i).hom (g k) ↦
      (pullbackSymmetry c.pt.hom (f k)).inv ≫ z ≫
        (pullbackSymmetry (D.obj i).hom (g k)).hom) (hbr k).2
    simpa only [overTransition_eq_symmetry, b₀, ar, f, g, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc] using H
  refine ⟨i, b, ?_⟩
  intro k
  let e := overInverseLimitPullbackComparison D c i
  let eA : pullback (f k) c.pt.hom ⟶
      pullback (pullback.snd (f k) (D.obj i).hom) (c.π.app i).left :=
    (e.hom.app (A k)).left
  let eB : pullback (g k) c.pt.hom ⟶
      pullback (pullback.snd (g k) (D.obj i).hom) (c.π.app i).left :=
    (e.hom.app (B k)).left
  let β : pullback (pullback.snd (f k) (D.obj i).hom) (c.π.app i).left ⟶
      pullback (pullback.snd (g k) (D.obj i).hom) (c.π.app i).left :=
    ((Over.pullback (c.π.app i).left).map (b k)).left
  have hβfst : β ≫ pullback.fst (pullback.snd (g k) (D.obj i).hom) (c.π.app i).left =
      pullback.fst (pullback.snd (f k) (D.obj i).hom) (c.π.app i).left ≫ b₀ k :=
    pullback.lift_fst _ _ _
  have hβsnd : β ≫ pullback.snd (pullback.snd (g k) (D.obj i).hom) (c.π.app i).left =
      pullback.snd (pullback.snd (f k) (D.obj i).hom) (c.π.app i).left :=
    pullback.lift_snd _ _ _
  have heAfst : eA ≫ pullback.fst (pullback.snd (f k) (D.obj i).hom) (c.π.app i).left =
      overInverseLimitTransition D c (A k) i :=
    overInverseLimitPullbackComparison_hom_fst D c (A k) i
  have heBfst : eB ≫ pullback.fst (pullback.snd (g k) (D.obj i).hom) (c.π.app i).left =
      overInverseLimitTransition D c (B k) i :=
    overInverseLimitPullbackComparison_hom_fst D c (B k) i
  have heAsnd : eA ≫ pullback.snd (pullback.snd (f k) (D.obj i).hom) (c.π.app i).left =
      pullback.snd (f k) c.pt.hom := overInverseLimitPullbackComparison_hom_snd D c (A k) i
  have heBsnd : eB ≫ pullback.snd (pullback.snd (g k) (D.obj i).hom) (c.π.app i).left =
      pullback.snd (g k) c.pt.hom := overInverseLimitPullbackComparison_hom_snd D c (B k) i
  apply Over.OverMorphism.ext
  change eA ≫ β = a₀ k ≫ eB
  apply pullback.hom_ext
  · rw [Category.assoc, hβfst, ← Category.assoc, heAfst, Category.assoc, heBfst]
    exact hrec k
  · rw [Category.assoc, hβsnd, heAsnd, Category.assoc, heBsnd, ha₀]

end AlgebraicGeometry.AffineTransitionHom
