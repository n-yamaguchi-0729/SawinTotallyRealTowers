/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Descent.AffineTransitionHom
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Simultaneous eventual equalities for inverse-limit models

A finite collection of recovered identities holds at one common tail stage.
The source and target models may vary with the equation. This is the finite
equation supplier needed for the inverse and triple-cocycle identities in
gluing descended finite-etale covers. No faithfulness of a limit projection
is assumed.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

/-- Finitely many equalities of stage-model morphisms which hold over the
actual limit already hold simultaneously after a single transition. The
indexing family is allowed to be empty. -/
theorem exists_eq_stage_family
    {I : Type u} [Category.{u} I] [IsCofiltered I] {S : Scheme.{u}}
    (D : I ⥤ Over S) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    {K : Type v} [Finite K] (Y Z : K → Scheme.{u})
    (f : ∀ k : K, Y k ⟶ S) (g : ∀ k : K, Z k ⟶ S)
    [∀ k : K, QuasiCompact (f k)] [∀ k : K, LocallyOfFiniteType (g k)]
    (i : I)
    (a b : ∀ k : K, pullback (D.obj i).hom (f k) ⟶ pullback (D.obj i).hom (g k))
    (ha : ∀ k : K, a k ≫ pullback.fst (D.obj i).hom (g k) =
      pullback.fst (D.obj i).hom (f k))
    (hb : ∀ k : K, b k ≫ pullback.fst (D.obj i).hom (g k) =
      pullback.fst (D.obj i).hom (f k))
    (hab : ∀ k : K, (cone D c (f k)).π.app i ≫ a k =
      (cone D c (f k)).π.app i ≫ b k) :
    ∃ (j : I) (hji : j ⟶ i), ∀ k : K,
      (diagram D (f k)).map hji ≫ a k = (diagram D (f k)).map hji ≫ b k := by
  classical
  choose j hji heq using fun k : K ↦
    exists_eq_stage D c hc (f k) (g k) i (a k) (b k) (ha k) (hb k) (hab k)
  obtain ⟨l, hli, hlj, hcomp⟩ := IsCofiltered.wideCospan hji
  refine ⟨l, hli, ?_⟩
  intro k
  rw [← hcomp k, Functor.map_comp, Category.assoc, Category.assoc, heq k]

end AlgebraicGeometry.AffineTransitionHom
