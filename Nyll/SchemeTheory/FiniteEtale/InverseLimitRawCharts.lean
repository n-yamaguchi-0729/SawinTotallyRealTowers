/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.InverseLimitFiniteCover
import Nyll.SchemeTheory.Gluing.RecoveredPullback
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Actual raw chart models of an inverse-limit cover

The finite affine chart models already constructed from the original cover
are transported through their proved cartesian chart squares to the literal
`Over.pullback` charts. This supplies exactly the recovery data consumed by
the generic raw-chart and overlap constructions.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

/-- Recovery on a cartesian chart transfers to recovery on the literal
chosen pullback chart. The comparison is constructed from the square. -/
def cartesianChartRecoveryIso
    {S L U C : Scheme.{u}} (ψ : L ⟶ S) (u : U ⟶ S)
    (a : C ⟶ U) (b : C ⟶ L) (h : IsPullback a b u ψ)
    (M : Over U) (X : Over L)
    (e : (Over.pullback a).obj M ≅ (Over.pullback b).obj X) :
    (Over.pullback (pullback.fst u ψ)).obj M ≅
      (Over.pullback (pullback.snd u ψ)).obj X := by
  let s : C ≅ pullback u ψ := h.isoPullback
  have ha : s.inv ≫ a = pullback.fst u ψ := h.isoPullback_inv_fst
  have hb : s.inv ≫ b = pullback.snd u ψ := h.isoPullback_inv_snd
  let eA : Over.pullback (pullback.fst u ψ) ≅ Over.pullback a ⋙ Over.pullback s.inv :=
    (eqToIso (congrArg (fun v : pullback u ψ ⟶ U ↦ Over.pullback v) ha)).symm ≪≫
      Over.pullbackComp s.inv a
  let eB : Over.pullback (pullback.snd u ψ) ≅ Over.pullback b ⋙ Over.pullback s.inv :=
    (eqToIso (congrArg (fun v : pullback u ψ ⟶ L ↦ Over.pullback v) hb)).symm ≪≫
      Over.pullbackComp s.inv b
  exact eA.app M ≪≫ (Over.pullback s.inv).mapIso e ≪≫ (eB.app X).symm

end AlgebraicGeometry.Scheme.Cover

namespace AlgebraicGeometry.FiniteEtale

open AlgebraicGeometry.Scheme.Cover

/-- An original finite-etale cover of the actual limit has finite-etale
models over a finite affine cover of a stage, with recovery on the literal
native pullback charts. No local model or recovery is assumed as input. -/
theorem exists_recovered_raw_chart_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    (i : I) [CompactSpace (D.obj i)] (X : FiniteEtale c.pt) :
    ∃ (j : I) (𝒰 : (D.obj j).OpenCover.{u}) (_ : Fintype 𝒰.I₀)
      (M : ∀ k : 𝒰.I₀, Over (𝒰.X k)),
      (∀ k : 𝒰.I₀, IsAffine (𝒰.X k)) ∧
      (∀ k : 𝒰.I₀, IsFiniteEtale (M k).hom) ∧
      Nonempty (∀ k : 𝒰.I₀,
        (Over.pullback (pullback.fst (𝒰.f k) (c.π.app j))).obj (M k) ≅
          (Over.pullback (pullback.snd (𝒰.f k) (c.π.app j))).obj
            ((FiniteEtale.forget c.pt).obj X)) := by
  obtain ⟨K, hK, U, _, hU, j, hji, hV, M, hM⟩ :=
    exists_recovered_finite_affine_cover_models D c hc i X
  have : Fintype K := hK
  let 𝒰 : (D.obj j).OpenCover.{u} :=
    Scheme.openCoverOfIsOpenCover (D.obj j) (fun k : K ↦ D.map hji ⁻¹ᵁ U k) hV
  let N (k : 𝒰.I₀) : Over (𝒰.X k) := (FiniteEtale.forget (𝒰.X k)).obj (M k)
  have hAffine (k : 𝒰.I₀) : IsAffine (𝒰.X k) := (hU k).preimage (D.map hji)
  have hFiniteEtale (k : 𝒰.I₀) : IsFiniteEtale (N k).hom :=
    inferInstanceAs (IsFiniteEtale (M k).hom)
  refine ⟨j, 𝒰, (show Fintype 𝒰.I₀ from hK), N, hAffine, hFiniteEtale, ⟨?_⟩⟩
  intro k
  let C : Scheme.{u} := (c.π.app i ⁻¹ᵁ U k).toScheme
  let a : C ⟶ 𝒰.X k := (opensCone D c i (U k)).π.app (Over.mk hji)
  let b : C ⟶ c.pt := (c.π.app i ⁻¹ᵁ U k).ι
  have hPB : IsPullback a b (𝒰.f k) (c.π.app j) := (hM k).1
  let e : (Over.pullback a).obj (N k) ≅
      (Over.pullback b).obj ((FiniteEtale.forget c.pt).obj X) :=
    (FiniteEtale.forget C).mapIso (hM k).2.some
  exact cartesianChartRecoveryIso (c.π.app j) (𝒰.f k) a b hPB
    (N k) ((FiniteEtale.forget c.pt).obj X) e

end AlgebraicGeometry.FiniteEtale
