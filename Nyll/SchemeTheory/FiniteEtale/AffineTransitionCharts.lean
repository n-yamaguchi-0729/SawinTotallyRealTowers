/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.AffineTransitionModel
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction

/-!
# Finite-etale chart models at a common inverse-system stage

The inverse images of an affine open at an original stage form an actual
affine inverse system. Descend each finite-etale chart cover through its
global-sections colimit, then use a finite cofiltered wide cospan to put all
models over the same stage. Native pullback composition preserves every
recovery isomorphism and the pulled-back opens still cover that stage.
-/

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

local instance finiteEtaleHasPullbacksAlongChart
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongChart
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]

include hc

/-- A cover of the inverse image of an affine stage open descends along
that open's actual tail diagram, with its native recovery map. -/
theorem exists_affine_chart_model (i : I) (U : (D.obj i).Opens) (hU : IsAffineOpen U)
    (X : FiniteEtale (opensCone D c i U).pt) :
    ∃ (j : Over i) (Xⱼ : FiniteEtale ((opensDiagram D i U).obj j)),
      Nonempty ((FiniteEtale.pullback ((opensCone D c i U).π.app j)).obj Xⱼ ≅ X) := by
  have : ∀ j : Over i, IsAffine ((opensDiagram D i U).obj j) :=
    fun j ↦ hU.preimage (D.map j.hom)
  exact exists_affine_inverse_limit_model
    (opensDiagram D i U) (opensCone D c i U) (isLimitOpensCone D c hc i U) X

/-- Finite-etale covers on the limit charts of a finite affine stage cover
have actual finite-etale models on one common stage cover. Every recovery
is along the original restricted cone projection. -/
theorem exists_common_stage_affine_chart_models
    (i : I) {K : Type v} [Finite K]
    (U : K → (D.obj i).Opens) (hcover : IsOpenCover U)
    (hU : ∀ k : K, IsAffineOpen (U k))
    (X : ∀ k : K, FiniteEtale (opensCone D c i (U k)).pt) :
    ∃ (j : I) (hji : j ⟶ i),
      IsOpenCover (fun k : K ↦ D.map hji ⁻¹ᵁ U k) ∧
      ∃ Xⱼ : ∀ k : K, FiniteEtale ((opensDiagram D i (U k)).obj (Over.mk hji)),
        ∀ k : K, Nonempty
          ((FiniteEtale.pullback ((opensCone D c i (U k)).π.app (Over.mk hji))).obj
            (Xⱼ k) ≅ X k) := by
  classical
  choose j Xj hj using fun k : K ↦ exists_affine_chart_model D c hc i (U k) (hU k) (X k)
  obtain ⟨l, hli, hlj, hcomp⟩ := IsCofiltered.wideCospan (fun k : K ↦ (j k).hom)
  let α (k : K) : Over.mk hli ⟶ j k := Over.homMk (hlj k) (hcomp k)
  let Y (k : K) : FiniteEtale ((opensDiagram D i (U k)).obj (Over.mk hli)) :=
    (FiniteEtale.pullback ((opensDiagram D i (U k)).map (α k))).obj (Xj k)
  refine ⟨l, hli, hcover.comap (D.map hli).base.hom, Y, ?_⟩
  intro k
  let p := (opensCone D c i (U k)).π.app (Over.mk hli)
  let q := (opensDiagram D i (U k)).map (α k)
  let r := (opensCone D c i (U k)).π.app (j k)
  have hpq : p ≫ q = r := (opensCone D c i (U k)).w (α k)
  let e₁ : FiniteEtale.pullback (p ≫ q) ≅
      FiniteEtale.pullback q ⋙ FiniteEtale.pullback p :=
    MorphismProperty.Over.pullbackComp
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) p q
  let e₂ : FiniteEtale.pullback (p ≫ q) ≅ FiniteEtale.pullback r :=
    MorphismProperty.Over.pullbackCongr
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤) hpq
  exact ⟨(e₁.app (Xj k)).symm ≪≫ e₂.app (Xj k) ≪≫ (hj k).some⟩

end AlgebraicGeometry.FiniteEtale
