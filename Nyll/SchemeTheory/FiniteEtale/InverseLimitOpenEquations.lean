/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Simultaneous equations over inverse-limit overlaps

Compact stage opens, including pairwise and triple intersections of affine
charts in a quasi-separated scheme, give actual quasi-compact restricted
inverse systems. A finite family of equations over different such opens
holds at one common original stage. Finiteness is required only over each
open, not over the ambient scheme.
-/

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Quasi-compactness of an open propagates to every stage of its actual
restricted inverse system under affine transition maps. -/
theorem opensDiagram_obj_compactSpace
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    (i : I) (U : (D.obj i).Opens) (hU : IsCompact (U : Set (D.obj i)))
    (j : Over i) : CompactSpace ((opensDiagram D i U).obj j) :=
  isCompact_iff_compactSpace.mp
    (QuasiCompact.isCompact_preimage (f := D.map j.hom) _ U.2 hU)

/-- The opens in the restricted inverse system inherit quasi-separatedness
from their actual ambient stages. -/
theorem opensDiagram_obj_quasiSeparatedSpace
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    (i : I) (U : (D.obj i).Opens) (j : Over i) :
    QuasiSeparatedSpace ((opensDiagram D i U).obj j) :=
  (isQuasiSeparated_iff_quasiSeparatedSpace _ (D.map j.hom ⁻¹ᵁ U).2).mp
    (.of_quasiSeparatedSpace _)

namespace FiniteEtale

local instance finiteEtaleOverCategoryOpenEquations (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) := instCategory X

local instance finiteEtaleHasPullbacksAlongOpenEquations
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongOpenEquations
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

private theorem map_eq_of_comparison
    {C₀ C₁ : Type*} [Category* C₀] [Category* C₁]
    {F G : C₀ ⥤ C₁} (e : F ≅ G) {A B : C₀} (a b : A ⟶ B)
    (h : G.map a = G.map b) : F.map a = F.map b := by
  apply (cancel_mono (e.hom.app B)).mp
  rw [e.hom.naturality, e.hom.naturality, h]

/-- A finite family of native equations over possibly different compact
stage opens descends simultaneously. The sources and targets need only be
finite etale over their respective opens. -/
theorem exists_inverse_limit_open_stage_map_eq_family
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    (i : I) {K : Type v} [Finite K]
    (U : K → (D.obj i).Opens)
    (hU : ∀ k : K, IsCompact (U k : Set (D.obj i)))
    (t : Over i)
    (A B : ∀ k : K, FiniteEtale ((opensDiagram D i (U k)).obj t))
    (a b : ∀ k : K, A k ⟶ B k)
    (hab : ∀ k : K,
      (FiniteEtale.pullback ((opensCone D c i (U k)).π.app t)).map (a k) =
        (FiniteEtale.pullback ((opensCone D c i (U k)).π.app t)).map (b k)) :
    ∃ (s : Over i) (hst : s ⟶ t), ∀ k : K,
      (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).map (a k) =
        (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).map (b k) := by
  classical
  have H (k : K) : ∃ (s : Over i) (hst : s ⟶ t),
      (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).map (a k) =
        (FiniteEtale.pullback ((opensDiagram D i (U k)).map hst)).map (b k) := by
    have : ∀ j : Over i, CompactSpace ((opensDiagram D i (U k)).obj j) :=
      opensDiagram_obj_compactSpace D i (U k) (hU k)
    exact exists_inverse_limit_stage_map_eq
      (opensDiagram D i (U k)) (opensCone D c i (U k))
      (isLimitOpensCone D c hc i (U k)) t (a k) (b k) (hab k)
  choose s hst hs using H
  obtain ⟨l, hlt, hls, hcomp⟩ := IsCofiltered.wideCospan hst
  refine ⟨l, hlt, ?_⟩
  intro k
  let E : FiniteEtale.pullback ((opensDiagram D i (U k)).map hlt) ≅
      FiniteEtale.pullback ((opensDiagram D i (U k)).map (hst k)) ⋙
        FiniteEtale.pullback ((opensDiagram D i (U k)).map (hls k)) :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
      ((opensDiagram D i (U k)).map (hls k))
      ((opensDiagram D i (U k)).map (hst k))
      ((opensDiagram D i (U k)).map hlt)
      (by rw [← Functor.map_comp, hcomp k])
  exact map_eq_of_comparison E (a k) (b k)
    (congrArg (FiniteEtale.pullback ((opensDiagram D i (U k)).map (hls k))).map (hs k))

end FiniteEtale

end AlgebraicGeometry
