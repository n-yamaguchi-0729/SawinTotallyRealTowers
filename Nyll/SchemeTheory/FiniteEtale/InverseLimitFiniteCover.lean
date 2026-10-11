/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.AffineTransitionLocalModel
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Actual finite affine covers for inverse-limit descent

Choose a finite affine cover of one quasi-compact original stage and descend
the restrictions of the given finite-etale cover of the limit. This produces
all chart models and their recovery isomorphisms at one common stage from
the original inverse system, without supplying a chart cover as extra data.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.FiniteEtale

/-- Every finite-etale cover of the inverse limit has recovered finite-etale
models over an actual finite affine cover at a common later original stage. -/
theorem exists_recovered_finite_affine_cover_models
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h)]
    (i : I) [CompactSpace (D.obj i)] (X : FiniteEtale c.pt) :
    ∃ (K : Type u) (_ : Fintype K) (U : K → (D.obj i).Opens),
      IsOpenCover U ∧ (∀ k : K, IsAffineOpen (U k)) ∧
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
  let 𝒰 : (D.obj i).OpenCover := (D.obj i).affineCover.finiteSubcover
  have : Fintype 𝒰.I₀ := inferInstanceAs
    (Fintype (D.obj i).affineCover.finiteSubcover.I₀)
  have : ∀ k : 𝒰.I₀, IsAffine (𝒰.X k) :=
    fun k ↦ inferInstanceAs (IsAffine (Spec _))
  let U : 𝒰.I₀ → (D.obj i).Opens := fun k ↦ (𝒰.f k).opensRange
  have hcover : IsOpenCover U := 𝒰.isOpenCover_opensRange
  have hU : ∀ k : 𝒰.I₀, IsAffineOpen (U k) :=
    fun k ↦ isAffineOpen_opensRange (𝒰.f k)
  exact ⟨𝒰.I₀, inferInstance, U, hcover, hU,
    exists_common_stage_recovered_local_models D c hc i U hcover hU X⟩

end AlgebraicGeometry.FiniteEtale
