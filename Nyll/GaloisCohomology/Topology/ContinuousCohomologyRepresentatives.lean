/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Tactic.Abel

/-! # Representatives and boundaries in continuous cohomology

The cocycle projection is surjective as a function, and its kernel consists
of boundaries. These are statements about the actual topological homology
objects, with no exactness assumptions on a coefficient sequence.
-/

open CategoryTheory CategoryTheory.Limits

namespace ContinuousCohomology

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

open TopRep ContRepresentation

/-- An actual homogeneous degree-two cocycle satisfies the alternating
four-point identity, with no restriction on its coefficient action. -/
theorem degreeTwo_cocycle_equation (X : TopRep.{v} R G)
    (z : ContinuousCohomology.cocycles X 2)
    (x₀ x₁ x₂ x₃ : G) :
    (((homogeneousCochains X).iCycles 2).hom z).1 x₁ x₂ x₃ -
        (((homogeneousCochains X).iCycles 2).hom z).1 x₀ x₂ x₃ +
        (((homogeneousCochains X).iCycles 2).hom z).1 x₀ x₁ x₃ -
      (((homogeneousCochains X).iCycles 2).hom z).1 x₀ x₁ x₂ = 0 := by
  let C := homogeneousCochains X
  let z₀ : C.X 2 := (C.iCycles 2).hom z
  have hz : (C.d 2 3).hom z₀ = 0 := by
    have h := congrArg (fun f ↦ TopModuleCat.Hom.hom f z) (C.iCycles_d 2 3)
    simpa only [z₀, TopModuleCat.hom_comp, ContinuousLinearMap.comp_apply,
      TopModuleCat.hom_zero, _root_.zero_apply] using h
  have hzEval := congrArg (fun τ : C.X 3 => τ.1 x₀ x₁ x₂ x₃) hz
  have hd := TopRep.homogeneousCochains.d_apply X 2 z₀
  have hdEval := congrArg (fun τ => τ x₀ x₁ x₂ x₃) hd
  rw [hdEval] at hzEval
  change z₀.1 x₁ x₂ x₃ - (z₀.1 x₀ x₂ x₃ -
    (z₀.1 x₀ x₁ x₃ - z₀.1 x₀ x₁ x₂)) = 0 at hzEval
  abel_nf at hzEval ⊢
  exact hzEval

/-- An actual homogeneous degree-two cocycle is equivariant for its
coefficient action. -/
theorem degreeTwo_equivariant (X : TopRep.{v} R G)
    (z : cocycles X 2) (g x₀ x₁ x₂ : G) :
    X.ρ g ((((homogeneousCochains X).iCycles 2).hom z).1 x₀ x₁ x₂) =
      (((homogeneousCochains X).iCycles 2).hom z).1
        (g * x₀) (g * x₁) (g * x₂) := by
  let z₀ := ((homogeneousCochains X).iCycles 2).hom z
  change (resolutionX X 3).ρ.invariants at z₀
  have h := congrArg (fun τ => τ (g * x₀) (g * x₁) (g * x₂)) (z₀.2 g)
  change X.ρ g (z₀.1 (g⁻¹ * (g * x₀)) (g⁻¹ * (g * x₁))
      (g⁻¹ * (g * x₂))) = z₀.1 (g * x₀) (g * x₁) (g * x₂) at h
  simpa only [inv_mul_cancel_left] using h

/-- Every continuous cohomology class has a homogeneous cocycle representative. -/
theorem π_surjective (A : TopRep.{v} R G) (n : ℕ) :
    Function.Surjective (π A n) := by
  let K := TopRep.homogeneousCochains A
  let S := K.sc n
  have hleft : Function.Surjective S.leftHomologyπ := by
    let c : CokernelCofork S.toCycles :=
      CokernelCofork.ofπ (TopModuleCat.cokerπ S.toCycles)
        (TopModuleCat.comp_cokerπ S.toCycles)
    let hc : IsColimit c := TopModuleCat.isColimitCoker S.toCycles
    let d : CokernelCofork S.toCycles :=
      CokernelCofork.ofπ S.leftHomologyπ S.leftHomologyData.wπ
    let hd : IsColimit d := S.leftHomologyData.hπ
    let e : c.pt ≅ d.pt := hc.coconePointUniqueUpToIso hd
    have he : TopModuleCat.cokerπ S.toCycles ≫ e.hom = S.leftHomologyπ := by
      exact hc.comp_coconePointUniqueUpToIso_hom hd WalkingParallelPair.one
    intro y
    obtain ⟨x, hx⟩ := TopModuleCat.cokerπ_surjective S.toCycles (e.inv y)
    refine ⟨x, ?_⟩
    rw [← he]
    change e.hom (TopModuleCat.cokerπ S.toCycles x) = y
    rw [hx]
    exact ConcreteCategory.congr_hom e.inv_hom_id y
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso S.leftHomologyIso.hom).2 y
  obtain ⟨x, hx⟩ := hleft z
  refine ⟨x, ?_⟩
  change S.leftHomologyIso.hom (S.leftHomologyπ x) = y
  rw [hx, hz]

/-- A homogeneous cocycle whose cohomology class is zero is a boundary. -/
theorem exists_boundary_of_π_eq_zero (A : TopRep.{v} R G) (n : ℕ)
    (z : cocycles A (n + 1)) (hz : π A (n + 1) z = 0) :
    ∃ c : (TopRep.homogeneousCochains A).X n,
      ((TopRep.homogeneousCochains A).d n (n + 1)).hom c =
        ((TopRep.homogeneousCochains A).iCycles (n + 1)).hom z := by
  let K := TopRep.homogeneousCochains A
  let S : ShortComplex (TopModuleCat R) :=
    ShortComplex.mk (K.toCycles n (n + 1)) (K.homologyπ (n + 1))
      (K.toCycles_comp_homologyπ n (n + 1))
  have hS : S.Exact := ShortComplex.exact_of_g_is_cokernel S
    (K.homologyIsCokernel n (n + 1) (CochainComplex.prev_nat_succ n))
  let F := forget₂ (TopModuleCat R) (ModuleCat R)
  have hSM : (S.map F).Exact := hS.map F
  obtain ⟨c, hc⟩ := ((S.map F).exact_iff_of_hasForget.mp hSM) z hz
  refine ⟨c, ?_⟩
  rw [← K.toCycles_i n (n + 1)]
  have hc' : (K.toCycles n (n + 1)).hom c = z := hc
  exact congrArg (fun w => (K.iCycles (n + 1)).hom w) hc'

end ContinuousCohomology
