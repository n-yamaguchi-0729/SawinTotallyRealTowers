/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoModels
import Nyll.SchemeTheory.FiniteEtale.InverseLimitOpenEquations
import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Actual overlap isomorphisms at one common stage

For a finite collection of compact opens, isomorphisms between limit
pullbacks of finite-etale models all descend to the same original stage.
Each overlap is treated over its own restricted inverse system; no cover
of an overlap is assumed finite etale over the entire ambient base.
-/

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

/-- Isomorphisms over finitely many compact stage opens descend to actual
isomorphisms at one common later stage, retaining each recovery equation. -/
theorem exists_inverse_limit_open_stage_iso_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) {K : Type v} [Finite K]
    (U : K → (D.obj i).Opens)
    (hU : ∀ k : K, IsCompact (U k : Set (D.obj i)))
    (t : Over i)
    (A B : ∀ k : K, FiniteEtale ((opensDiagram D i (U k)).obj t))
    (a : ∀ k : K,
      (FiniteEtale.pullback ((opensCone D c i (U k)).π.app t)).obj (A k) ≅
        (FiniteEtale.pullback ((opensCone D c i (U k)).π.app t)).obj (B k)) :
    ∃ (s : Over i) (hst : s ⟶ t)
      (b : ∀ k : K,
        (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).obj (A k) ≅
          (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).obj (B k)),
      ∀ k : K,
        (inverseLimitPullbackComparison (opensDiagram D i (U k))
            (opensCone D c i (U k)) hst).hom.app (A k) ≫
            (FiniteEtale.pullback ((opensCone D c i (U k)).π.app s)).map (b k).hom =
          (a k).hom ≫
            (inverseLimitPullbackComparison (opensDiagram D i (U k))
              (opensCone D c i (U k)) hst).hom.app (B k) := by
  classical
  have H (k : K) : ∃ (s : Over i) (hst : s ⟶ t)
      (b : (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).obj (A k) ≅
        (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).obj (B k)),
      (inverseLimitPullbackComparison (opensDiagram D i (U k))
          (opensCone D c i (U k)) hst).hom.app (A k) ≫
          (FiniteEtale.pullback ((opensCone D c i (U k)).π.app s)).map b.hom =
        (a k).hom ≫
          (inverseLimitPullbackComparison (opensDiagram D i (U k))
            (opensCone D c i (U k)) hst).hom.app (B k) := by
    have : ∀ j : Over i, CompactSpace ((opensDiagram D i (U k)).obj j) :=
      opensDiagram_obj_compactSpace D i (U k) (hU k)
    have : ∀ j : Over i, QuasiSeparatedSpace ((opensDiagram D i (U k)).obj j) :=
      opensDiagram_obj_quasiSeparatedSpace D i (U k)
    exact exists_inverse_limit_stage_iso
      (opensDiagram D i (U k)) (opensCone D c i (U k))
      (isLimitOpensCone D c hc i (U k)) t (A k) (B k) (a k)
  choose s hst b hb using H
  obtain ⟨l, hlt, hls, hcomp⟩ := IsCofiltered.wideCospan hst
  have H' (k : K) : ∃ b' :
      (FiniteEtale.pullback ((opensDiagram D i (U k)).map hlt)).obj (A k) ≅
        (FiniteEtale.pullback ((opensDiagram D i (U k)).map hlt)).obj (B k),
      (inverseLimitPullbackComparison (opensDiagram D i (U k))
          (opensCone D c i (U k)) hlt).hom.app (A k) ≫
          (FiniteEtale.pullback ((opensCone D c i (U k)).π.app l)).map b'.hom =
        (a k).hom ≫
          (inverseLimitPullbackComparison (opensDiagram D i (U k))
            (opensCone D c i (U k)) hlt).hom.app (B k) := by
    rw [← hcomp k]
    exact exists_inverse_limit_stage_iso_later
      (opensDiagram D i (U k)) (opensCone D c i (U k))
      (hst k) (hls k) (A k) (B k) (a k) (b k) (hb k)
  choose b' hb' using H'
  exact ⟨l, hlt, b', hb'⟩

end AlgebraicGeometry.FiniteEtale
