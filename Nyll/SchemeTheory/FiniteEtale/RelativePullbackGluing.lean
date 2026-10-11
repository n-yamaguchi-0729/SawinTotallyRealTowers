/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RelativePullback
import Nyll.SchemeTheory.Gluing.RecoveredPullback
import Nyll.SchemeTheory.FiniteEtale.RelativeGluing

/-!
# Finite-etale structure on the actual pulled-back gluing

The gluing relations proved at a later inverse-system stage give actual
scheme gluing data. Its local structure morphisms are base changes of the
original finite-etale maps; their cartesian overlap squares construct a
finite-etale structural morphism to the later base.
-/

noncomputable section

universe u

open CategoryTheory Limits
open AlgebraicGeometry.Scheme.Cover

namespace AlgebraicGeometry.FiniteEtale

variable {S T : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over S) (V : 𝒰.I₀ × 𝒰.I₀ → Over S)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (hy : ∀ i : 𝒰.I₀, y i ≫ 𝒰.f i = (A i).hom)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))
variable (t : ∀ i j : 𝒰.I₀, V (i, j) ⟶ V (j, i))
variable (ht : ∀ i j : 𝒰.I₀, (t i j).left ≫ (d j i).left ≫ y j = ℓ i j)
variable (ψ : T ⟶ S)
variable (hdiag : ∀ i : 𝒰.I₀,
  (Over.pullback ψ).map (t i i) = 𝟙 ((Over.pullback ψ).obj (V (i, i))))
variable (hcycle : ∀ i j k : 𝒰.I₀,
  (Over.pullback ψ).map
      (relativeTripleTransition 𝒰 A V d y ℓ hV t ht i j k ≫
        relativeTripleTransition 𝒰 A V d y ℓ hV t ht j k i ≫
          relativeTripleTransition 𝒰 A V d y ℓ hV t ht k i j) =
    𝟙 ((Over.pullback ψ).obj (relativeTriple 𝒰 A V d i j k)))

include hy in
/-- Gluing the actual pulled-back finite-etale local models produces an
actual finite-etale morphism, compatible with every native chart map. -/
theorem exists_relativePullbackGlue_finiteEtale [∀ i : 𝒰.I₀, IsFiniteEtale (y i)] :
    ∃ q : (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).glued ⟶ T,
      IsFiniteEtale q ∧ ∀ i : 𝒰.I₀,
        (relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle).ι i ≫ q =
          ((Over.pullback ψ).obj (A i)).hom := by
  have hyfinite : ∀ i : 𝒰.I₀, IsFiniteEtale (y i) := inferInstance
  let G := relativeGlueDataOfPullbackEquations 𝒰 A V d y ℓ hV t ht ψ hdiag hcycle
  let Q := Over.pullback ψ
  let F : Over S ⥤ Scheme.{u} := relativeRecoveryFunctor ψ
  let 𝒲 : T.OpenCover := swappedPullbackCover ψ 𝒰
  let Y (i : 𝒰.I₀) : A i ⟶ gluingChartOver 𝒰 i := Over.homMk (y i) (hy i)
  let L (i j : 𝒰.I₀) : V (i, j) ⟶ gluingChartOver 𝒰 j :=
    Over.homMk (ℓ i j) (by
      calc
        ℓ i j ≫ 𝒰.f j = (d i j).left ≫ (y i ≫ 𝒰.f i) := (hV i j).w.symm
        _ = (V (i, j)).hom := by rw [hy, Over.w])
  let y' (i : 𝒰.I₀) : G.U i ⟶ 𝒲.X i := (Q.map (Y i)).left
  let ℓ' (i j : 𝒰.I₀) : G.V (i, j) ⟶ 𝒲.X j := (Q.map (L i j)).left
  have : ∀ i : G.J, IsOpenImmersion (𝒲.f i) := fun i ↦ 𝒲.map_prop i
  have : ∀ i : G.J, IsFiniteEtale (y' i) := by
    intro i
    exact MorphismProperty.of_isPullback (P := @IsFiniteEtale)
      (relativePullback_map_isPullback ψ (Y i)).flip
      (hyfinite (show 𝒰.I₀ from i))
  have hV' (i j : G.J) : IsPullback (G.f i j) (ℓ' i j) (y' i ≫ 𝒲.f i) (𝒲.f j) := by
    have h₀ : IsPullback (d i j).left (L i j).left (A i).hom (gluingChartOver 𝒰 j).hom := by
      change IsPullback (d i j).left (ℓ i j) (A i).hom (𝒰.f j)
      rw [← hy i]
      exact hV i j
    have H := overPullback_product_isPullback ψ (d i j) (L i j) h₀
    change IsPullback ((Q.map (d i j)).left) ((Q.map (L i j)).left)
      ((Q.map (Y i)).left ≫ (Q.obj (gluingChartOver 𝒰 i)).hom)
      (Q.obj (gluingChartOver 𝒰 j)).hom
    rw [Over.w (Q.map (Y i))]
    exact H
  have ht' (i j : G.J) : G.t i j ≫ G.f j i ≫ y' j = ℓ' i j := by
    have H : t i j ≫ d j i ≫ Y j = L i j := by
      apply Over.OverMorphism.ext
      exact ht i j
    exact (congrArg (fun a ↦ F.map (t i j) ≫ a) (F.map_comp (d j i) (Y j))).symm.trans
      ((F.map_comp (t i j) (d j i ≫ Y j)).symm.trans (congrArg F.map H))
  obtain ⟨q, hq, hqU⟩ := G.exists_finiteEtale_gluedToBase T 𝒲.X 𝒲.f
    𝒲.exists_eq y' ℓ' hV' ht'
  refine ⟨q, hq, ?_⟩
  intro i
  exact (hqU i).w.symm.trans (Over.w (Q.map (Y i)))

end AlgebraicGeometry.FiniteEtale
