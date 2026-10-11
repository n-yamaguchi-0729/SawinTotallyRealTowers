/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.AffineTransitionCharts
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Recovered local models of an actual finite-etale cover

Starting with one cover of the inverse limit, restrict it to a finite affine
stage cover and construct all local finite-etale models at one later stage.
The restricted cone maps are proved cartesian, so the recovery maps identify
the actual base changes of these charts.
-/

noncomputable section

universe u v

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

/-- Each restricted cone map is the actual base change of the original
cone projection along the corresponding open immersion. -/
theorem opensCone_isPullback
    {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (i : I) (U : (D.obj i).Opens) (j : Over i) :
    IsPullback ((opensCone D c i U).π.app j) (c.π.app i ⁻¹ᵁ U).ι
      (D.map j.hom ⁻¹ᵁ U).ι (c.π.app j.left) := by
  apply IsOpenImmersion.isPullback
    (U := (c.π.app i ⁻¹ᵁ U).toScheme) (V := (D.map j.hom ⁻¹ᵁ U).toScheme)
    (X := c.pt) (Y := D.obj j.left)
  · exact (Scheme.Hom.resLE_comp_ι (c.π.app j.left) _).symm
  · rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι,
      ← Scheme.Hom.comp_preimage, c.w]

namespace FiniteEtale

/-- A finite-etale cover of the limit has recovered local models on one
actual later finite affine cover, with every chart square proved cartesian. -/
theorem exists_common_stage_recovered_local_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    (i : I) {K : Type v} [Finite K]
    (U : K → (D.obj i).Opens) (hcover : IsOpenCover U)
    (hU : ∀ k : K, IsAffineOpen (U k)) (X : FiniteEtale c.pt) :
    ∃ (j : I) (hji : j ⟶ i),
      IsOpenCover (fun k : K ↦ D.map hji ⁻¹ᵁ U k) ∧
      ∃ M : ∀ k : K, FiniteEtale ((opensDiagram D i (U k)).obj (Over.mk hji)),
        ∀ k : K,
          IsPullback ((opensCone D c i (U k)).π.app (Over.mk hji))
            (c.π.app i ⁻¹ᵁ U k).ι (D.map hji ⁻¹ᵁ U k).ι (c.π.app j) ∧
          Nonempty
            ((FiniteEtale.pullback ((opensCone D c i (U k)).π.app (Over.mk hji))).obj
                (M k) ≅
              (FiniteEtale.pullback (c.π.app i ⁻¹ᵁ U k).ι).obj X) := by
  let XU (k : K) : FiniteEtale (opensCone D c i (U k)).pt :=
    (FiniteEtale.pullback (c.π.app i ⁻¹ᵁ U k).ι).obj X
  obtain ⟨j, hji, hV, M, hM⟩ :=
    exists_common_stage_affine_chart_models D c hc i U hcover hU XU
  exact ⟨j, hji, hV, M, fun k ↦
    ⟨opensCone_isPullback D c i (U k) (Over.mk hji), hM k⟩⟩

end FiniteEtale

end AlgebraicGeometry
