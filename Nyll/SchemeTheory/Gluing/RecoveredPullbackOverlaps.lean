/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RecoveredPullback
import Nyll.SchemeTheory.Gluing.CommonCover

/-!
# Actual overlaps of the recovered pullback charts

The canonical recovered transition identifies the two chart overlaps inside
the original recovered scheme. The cartesian assertion follows from the
already proved chart squares and transition projection equations.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

/-- The actual recovered raw overlap is the pullback of the two recovered
chart maps into the original scheme, for an arbitrary base change. -/
theorem recoveredPullbackTransition_isPullback
    {S L : Scheme.{u}} (ψ : L ⟶ S) (𝒰 : S.OpenCover.{u})
    (M : ∀ i : 𝒰.I₀, Over (𝒰.X i)) (Z : Over L)
    (e : ∀ i : 𝒰.I₀,
      (Over.pullback (pullback.fst (𝒰.f i) ψ)).obj (M i) ≅
        (Over.pullback (pullback.snd (𝒰.f i) ψ)).obj Z)
    (i j : 𝒰.I₀) :
    IsPullback ((Over.pullback ψ).map (gluingOverlapFirst 𝒰 M i j)).left
      (recoveredPullbackTransition ψ 𝒰 M Z e i j ≫
        (Over.pullback ψ).map (gluingOverlapFirst 𝒰 M j i)).left
      (recoveredPullbackChartMap ψ 𝒰 M Z e i)
      (recoveredPullbackChartMap ψ 𝒰 M Z e j) := by
  let F := Over.pullback ψ
  let hi := recoveredPullbackChartMap ψ 𝒰 M Z e i
  let hj := recoveredPullbackChartMap ψ 𝒰 M Z e j
  let yi := (F.map (gluingLocalStructure 𝒰 M i)).left
  let yj := (F.map (gluingLocalStructure 𝒰 M j)).left
  let ui := (F.obj (gluingChartOver 𝒰 i)).hom
  let uj := (F.obj (gluingChartOver 𝒰 j)).hom
  let d := (F.map (gluingOverlapFirst 𝒰 M i j)).left
  let r := (recoveredPullbackTransition ψ 𝒰 M Z e i j ≫
    F.map (gluingOverlapFirst 𝒰 M j i)).left
  let ℓ := (F.map (gluingOverlapSecond 𝒰 M i j)).left
  have ha : yi ≫ ui = hi ≫ Z.hom :=
    (Over.w (F.map (gluingLocalStructure 𝒰 M i))).trans
      (recoveredPullbackChartMap_structure ψ 𝒰 M Z e i).symm
  have hc : IsPullback yj hj uj Z.hom :=
    recoveredPullbackChartMap_isPullback ψ 𝒰 M Z e j
  have hV : IsPullback d ℓ (yi ≫ ui) uj := by
    have hw : yi ≫ ui = (F.obj (gluingLocalOver 𝒰 M i)).hom :=
      Over.w (F.map (gluingLocalStructure 𝒰 M i))
    rw [hw]
    exact recoveredPullbackOverlap_isPullback ψ 𝒰 M i j
  have hr : r ≫ yj = ℓ :=
    (congrArg (fun z ↦ z ≫ yj)
      (recoveredPullbackTransition_first ψ 𝒰 M Z e i j)).trans
        (recoveredPullbackOverlapTransfer_structure ψ 𝒰 M Z e i j)
  have hcompat : d ≫ hi = r ≫ hj := by
    exact ((Category.assoc _ _ _).trans
      (recoveredPullbackTransition_chartMap ψ 𝒰 M Z e i j)).symm
  exact isPullback_of_cartesian_chart_overlap hi hj Z.hom yi yj ui uj d r ℓ ha hc hV hr hcompat

end AlgebraicGeometry.Scheme.Cover
