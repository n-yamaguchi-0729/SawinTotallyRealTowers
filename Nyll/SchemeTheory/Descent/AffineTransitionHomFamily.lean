/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Simultaneous actual morphism descent for finitely many models

First descend each map, then project its target to the fixed original model.
Transport these projected maps along a finite cofiltered cone and reconstruct
the maps between stage pullbacks. This retains every original recovery square
and does not require an overlap model to be finite over the entire base.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

/-- Finitely many morphisms of pulled-back qcqs models, with locally finitely
presented targets, descend to a single actual coefficient stage. -/
theorem exists_hom_stage_family
    {I : Type u} [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}}
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    {K : Type v} [Finite K] (Y Z : K → Scheme.{u})
    (f : ∀ k : K, Y k ⟶ S) (g : ∀ k : K, Z k ⟶ S)
    [∀ k : K, QuasiCompact (f k)] [∀ k : K, QuasiSeparated (f k)]
    [∀ k : K, LocallyOfFinitePresentation (g k)]
    (a : ∀ k : K, pullback c.pt.hom (f k) ⟶ pullback c.pt.hom (g k))
    (ha : ∀ k : K, a k ≫ pullback.fst c.pt.hom (g k) = pullback.fst c.pt.hom (f k)) :
    ∃ (i : I) (b : ∀ k : K, pullback (D.obj i).hom (f k) ⟶
      pullback (D.obj i).hom (g k)), ∀ k : K,
        b k ≫ pullback.fst (D.obj i).hom (g k) = pullback.fst (D.obj i).hom (f k) ∧
        (cone D c (f k)).π.app i ≫ b k = a k ≫ (cone D c (g k)).π.app i := by
  classical
  have H (k : K) : ∃ (i : I) (b : pullback (D.obj i).hom (f k) ⟶ Z k),
      (cone D c (f k)).π.app i ≫ b = a k ≫ pullback.snd c.pt.hom (g k) ∧
      b ≫ g k = pullback.snd (D.obj i).hom (f k) ≫ f k := by
    obtain ⟨i, b, hb, hrec⟩ := exists_hom_stage D c hc (f k) (g k) (a k) (ha k)
    refine ⟨i, b ≫ pullback.snd (D.obj i).hom (g k), ?_, ?_⟩
    · rw [← Category.assoc, hrec, Category.assoc, cone_map_snd]
    · rw [Category.assoc, ← pullback.condition (f := (D.obj i).hom) (g := g k),
        ← Category.assoc, hb, pullback.condition]
  choose j b hb hbS using H
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image j)
  let h (k : K) : l ⟶ j k :=
    (hl (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)).some
  let q (k : K) : pullback (D.obj l).hom (f k) ⟶ Z k :=
    (diagram D (f k)).map (h k) ≫ b k
  have hqS (k : K) : q k ≫ g k = pullback.snd (D.obj l).hom (f k) ≫ f k := by
    have hsnd : (diagram D (f k)).map (h k) ≫ pullback.snd (D.obj (j k)).hom (f k) =
        pullback.snd (D.obj l).hom (f k) :=
      Over.w ((Over.pullback (f k)).map (D.map (h k)))
    change ((diagram D (f k)).map (h k) ≫ b k) ≫ g k = _
    rw [Category.assoc, hbS k, ← Category.assoc, hsnd]
  have hq (k : K) : (cone D c (f k)).π.app l ≫ q k =
      a k ≫ pullback.snd c.pt.hom (g k) := by
    change (cone D c (f k)).π.app l ≫ ((diagram D (f k)).map (h k) ≫ b k) = _
    rw [← Category.assoc, (cone D c (f k)).w (h k), hb k]
  let b' (k : K) : pullback (D.obj l).hom (f k) ⟶ pullback (D.obj l).hom (g k) :=
    pullback.lift (pullback.fst (D.obj l).hom (f k)) (q k)
      ((pullback.condition (f := (D.obj l).hom) (g := f k)).trans (hqS k).symm)
  refine ⟨l, b', ?_⟩
  intro k
  refine ⟨pullback.lift_fst _ _ _, ?_⟩
  apply pullback.hom_ext
  · change ((cone D c (f k)).π.app l ≫ b' k) ≫ pullback.fst (D.obj l).hom (g k) =
      (a k ≫ (cone D c (g k)).π.app l) ≫ pullback.fst (D.obj l).hom (g k)
    rw [Category.assoc, pullback.lift_fst, cone_map_fst,
      Category.assoc, cone_map_fst, ← Category.assoc, ha k]
  · change ((cone D c (f k)).π.app l ≫ b' k) ≫ pullback.snd (D.obj l).hom (g k) =
      (a k ≫ (cone D c (g k)).π.app l) ≫ pullback.snd (D.obj l).hom (g k)
    rw [Category.assoc, pullback.lift_snd, hq k, Category.assoc, cone_map_snd]

end AlgebraicGeometry.AffineTransitionHom
