/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RecoveredPullback
import Nyll.SchemeTheory.Gluing.RelativeOverlap
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Actual relative chart data after a base change

Base change of local models and their actual overlaps retains the chart
structure morphisms, finite-etaleness, and cartesian overlap squares. Any
transition morphism over the new base then preserves the second chart
structure map, with no faithful-base-change assumption.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {S T : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over S) (V : 𝒰.I₀ × 𝒰.I₀ → Over S)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (hy : ∀ i : 𝒰.I₀, y i ≫ 𝒰.f i = (A i).hom)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))

include hy in
/-- The actual local structural morphism regarded as a map over the ambient base. -/
def relativeChartStructure (i : 𝒰.I₀) : A i ⟶ gluingChartOver 𝒰 i :=
  Over.homMk (y i) (hy i)

include hy hV in
/-- The second projection from an actual overlap, regarded as a map over the base. -/
def relativeChartOverlapSecond (i j : 𝒰.I₀) : V (i, j) ⟶ gluingChartOver 𝒰 j :=
  Over.homMk (ℓ i j) (by
    calc
      ℓ i j ≫ 𝒰.f j = (d i j).left ≫ (y i ≫ 𝒰.f i) := (hV i j).w.symm
      _ = (V (i, j)).hom := by rw [hy, Over.w])

variable (φ : T ⟶ S)

include hy in
/-- The actual base-changed local structural map to the base-changed chart. -/
def relativeBaseChangedChartStructure (i : 𝒰.I₀) :
    ((Over.pullback φ).obj (A i)).left ⟶ (swappedPullbackCover φ 𝒰).X i :=
  ((Over.pullback φ).map (relativeChartStructure 𝒰 A y hy i)).left

include hy hV in
/-- The actual second projection of a base-changed overlap. -/
def relativeBaseChangedOverlapSecond (i j : 𝒰.I₀) :
    ((Over.pullback φ).obj (V (i, j))).left ⟶ (swappedPullbackCover φ 𝒰).X j :=
  ((Over.pullback φ).map (relativeChartOverlapSecond 𝒰 A V d y hy ℓ hV i j)).left

/-- Base-changed local maps have their literal ambient structural morphism. -/
theorem relativeBaseChangedChartStructure_base (i : 𝒰.I₀) :
    relativeBaseChangedChartStructure 𝒰 A y hy φ i ≫ (swappedPullbackCover φ 𝒰).f i =
      ((Over.pullback φ).obj (A i)).hom :=
  Over.w ((Over.pullback φ).map (relativeChartStructure 𝒰 A y hy i))

/-- Base change preserves finite-etaleness of the actual local chart map. -/
theorem relativeBaseChangedChartStructure_finiteEtale
    [∀ i : 𝒰.I₀, IsFiniteEtale (y i)] (i : 𝒰.I₀) :
    IsFiniteEtale (relativeBaseChangedChartStructure 𝒰 A y hy φ i) :=
  MorphismProperty.of_isPullback (P := @IsFiniteEtale)
    (overCoefficientPullback_isPullback φ (relativeChartStructure 𝒰 A y hy i)).flip
    (inferInstanceAs (IsFiniteEtale (y i)))

/-- Cartesian pairwise overlaps remain the actual cartesian overlaps over
the base-changed open charts. -/
theorem relativeBaseChangedOverlap_isPullback (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback φ).map (d i j)).left
      (relativeBaseChangedOverlapSecond 𝒰 A V d y hy ℓ hV φ i j)
      (relativeBaseChangedChartStructure 𝒰 A y hy φ i ≫ (swappedPullbackCover φ 𝒰).f i)
      ((swappedPullbackCover φ 𝒰).f j) := by
  have h₀ : IsPullback (d i j).left
      (relativeChartOverlapSecond 𝒰 A V d y hy ℓ hV i j).left
      (A i).hom (gluingChartOver 𝒰 j).hom := by
    change IsPullback (d i j).left (ℓ i j) (A i).hom (𝒰.f j)
    rw [← hy i]
    exact hV i j
  rw [relativeBaseChangedChartStructure_base]
  exact overPullback_product_isPullback φ (d i j)
    (relativeChartOverlapSecond 𝒰 A V d y hy ℓ hV i j) h₀

/-- Any transition over the new ambient base preserves the second chart
structural map because open chart maps are monomorphisms. -/
theorem relativeBaseChangedTransition_structure
    (t : ∀ i j : 𝒰.I₀,
      (Over.pullback φ).obj (V (i, j)) ⟶ (Over.pullback φ).obj (V (j, i)))
    (i j : 𝒰.I₀) :
    (t i j).left ≫ ((Over.pullback φ).map (d j i)).left ≫
        relativeBaseChangedChartStructure 𝒰 A y hy φ j =
      relativeBaseChangedOverlapSecond 𝒰 A V d y hy ℓ hV φ i j := by
  let uj : (swappedPullbackCover φ 𝒰).X j ⟶ T := (swappedPullbackCover φ 𝒰).f j
  have : IsOpenImmersion uj := (swappedPullbackCover φ 𝒰).map_prop j
  apply (cancel_mono uj).mp
  dsimp only [uj]
  rw [Category.assoc, Category.assoc, relativeBaseChangedChartStructure_base,
    Over.w, Over.w]
  exact (Over.w ((Over.pullback φ).map
    (relativeChartOverlapSecond 𝒰 A V d y hy ℓ hV i j))).symm

/-- Quasi-compact base change preserves compactness of the actual open chart. -/
theorem relativeBaseChangedChart_compactSpace [QuasiCompact φ]
    (i : 𝒰.I₀) [CompactSpace (𝒰.X i)] :
    CompactSpace ((swappedPullbackCover φ 𝒰).X i) :=
  inferInstanceAs (CompactSpace (Limits.pullback (C := Scheme.{u}) (𝒰.f i) φ))

end AlgebraicGeometry.Scheme.Cover
