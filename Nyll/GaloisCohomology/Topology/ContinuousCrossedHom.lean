/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.ContinuousCohomologyRepresentatives

/-! # Continuous crossed homomorphisms and homogeneous one-cocycles -/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous crossed homomorphism for a topological integral representation. -/
structure CrossedHom (X : TopRep.{u} ℤ G) where
  /-- The function giving the crossed-homomorphism values. -/
  toFun : G → X
  /-- Continuity of the crossed-homomorphism value function. -/
  continuous_toFun : Continuous toFun
  /-- The crossed-homomorphism identity for the given representation action. -/
  map_mul : ∀ g h, toFun (g * h) = toFun g + X.ρ g (toFun h)

namespace CrossedHom

variable {X : TopRep.{u} ℤ G}

omit [IsTopologicalGroup G] in
theorem map_one (c : CrossedHom X) : c.toFun 1 = 0 := by
  have hc := c.map_mul 1 1
  rw [one_mul, _root_.map_one X.ρ, one_apply_eq_self] at hc
  exact add_eq_left.mp hc.symm

/-- The homogeneous cocycle is the difference of the two inhomogeneous values. -/
def homogeneous (c : CrossedHom X) : (homogeneousCochains X).X 1 := by
  let σ : C(G, C(G, X)) := ContinuousMap.curry
    ⟨fun z : G × G => c.toFun z.2 - c.toFun z.1,
      (c.continuous_toFun.comp continuous_snd).sub
        (c.continuous_toFun.comp continuous_fst)⟩
  refine ⟨σ, ?_⟩
  intro a
  ext g h
  change X.ρ a (c.toFun (a⁻¹ * h) - c.toFun (a⁻¹ * g)) = c.toFun h - c.toFun g
  rw [map_sub]
  have hg := c.map_mul a (a⁻¹ * g)
  have hh := c.map_mul a (a⁻¹ * h)
  rw [mul_inv_cancel_left] at hg hh
  rw [hh, hg]
  abel

theorem homogeneous_apply (c : CrossedHom X) (g h : G) :
    c.homogeneous.1 g h = c.toFun h - c.toFun g := rfl

theorem homogeneous_mem_cycles (c : CrossedHom X) :
    ((homogeneousCochains X).d 1 2).hom c.homogeneous = 0 := by
  apply Subtype.ext
  ext g h k
  have hd := homogeneousCochains.d_apply X 1 c.homogeneous
  have hdh := congrArg (fun τ => τ g h k) hd
  rw [hdh]
  simp only [d_succ, d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ConcreteCategory.hom_ofHom]
  change (c.toFun k - c.toFun h) -
    ((c.toFun k - c.toFun g) - (c.toFun h - c.toFun g)) = 0
  abel

local instance {R : Type} [Ring R] [TopologicalSpace R] [DiscreteTopology R] :
    ContinuousSMul R (ULift.{u} R) := ⟨continuous_of_discreteTopology⟩

private def scalarLine {R : Type} [Ring R] [TopologicalSpace R] [DiscreteTopology R]
    {M : TopModuleCat.{u} R} (x : M) :
    TopModuleCat.of R (ULift.{u} R) ⟶ M := by
  exact TopModuleCat.ofHom
    { toLinearMap :=
        { toFun := fun a => a.down • x
          map_add' := fun a b => add_smul a.down b.down x
          map_smul' := fun a b => mul_smul a b.down x }
      cont := continuous_of_discreteTopology }

private theorem scalarLine_one {R : Type} [Ring R] [TopologicalSpace R] [DiscreteTopology R]
    {M : TopModuleCat.{u} R} (x : M) : scalarLine x (ULift.up 1) = x :=
  one_smul R x

private theorem scalarLine_comp_eq_zero
    {R : Type} [Ring R] [TopologicalSpace R] [DiscreteTopology R]
    {M N : TopModuleCat.{u} R} (x : M) (f : M ⟶ N) (hx : f.hom x = 0) :
    scalarLine x ≫ f = 0 := by
  ext a
  change f.hom (a.down • x) = 0
  rw [map_smul, hx, smul_zero]

/-- A crossed homomorphism determines an actual homogeneous one-cocycle. -/
noncomputable def toCocycle (c : CrossedHom X) : cocycles X 1 := by
  let line := scalarLine c.homogeneous
  have hline : line ≫ (homogeneousCochains X).d 1 2 = 0 :=
    scalarLine_comp_eq_zero c.homogeneous _ c.homogeneous_mem_cycles
  exact ((homogeneousCochains X).liftCycles line 2 (CochainComplex.next ℕ 1) hline) (ULift.up 1)

theorem iCycles_toCocycle (c : CrossedHom X) :
    (homogeneousCochains X).iCycles 1 c.toCocycle = c.homogeneous := by
  change (homogeneousCochains X).iCycles 1
    (((homogeneousCochains X).liftCycles (scalarLine c.homogeneous) 2
      (CochainComplex.next ℕ 1) _) (ULift.up 1)) = _
  rw [← ConcreteCategory.comp_apply, (homogeneousCochains X).liftCycles_i]
  exact scalarLine_one c.homogeneous

end CrossedHom

/-- Dehomogenization of a homogeneous one-cocycle. -/
noncomputable def crossedHomOfCocycle (X : TopRep.{u} ℤ G) (z : cocycles X 1) :
    CrossedHom X := by
  let σ := (homogeneousCochains X).iCycles 1 z
  have hσ (g h k : G) : σ.1 h k - (σ.1 g k - σ.1 g h) = 0 := by
    have hz := ConcreteCategory.congr_hom ((homogeneousCochains X).iCycles_d 1 2) z
    have hd := homogeneousCochains.d_apply X 1 σ
    have hdh := congrArg (fun τ => τ g h k) hd
    have hz' := congrArg (fun τ => τ.1 g h k) hz
    change (((homogeneousCochains X).d 1 2).hom σ).1 g h k = 0 at hz'
    rw [hdh] at hz'
    simp only [d_succ, d_zero, TopRep.hom_sub,
      ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
      ContinuousMap.const_apply, ContinuousMap.comp_apply, ConcreteCategory.hom_ofHom,
      ContinuousMap.sub_apply] at hz'
    exact hz'
  refine ⟨fun g => σ.1 1 g, (σ.1 1).continuous, ?_⟩
  intro g h
  have hinv := congrArg (fun τ => τ g (g * h)) (σ.2 g)
  have hinv' : X.ρ g (σ.1 1 h) = σ.1 g (g * h) := by
    simpa only [coind₁_apply_apply, inv_mul_cancel, inv_mul_cancel_left] using hinv
  have hc := hσ 1 g (g * h)
  rw [← hinv'] at hc
  exact (eq_sub_iff_add_eq.mp (sub_eq_zero.mp hc)).symm.trans (add_comm _ _)

theorem crossedHomOfCocycle_toCocycle (X : TopRep.{u} ℤ G) (c : CrossedHom X) (g : G) :
    (crossedHomOfCocycle X c.toCocycle).toFun g = c.toFun g := by
  change ((homogeneousCochains X).iCycles 1 c.toCocycle).1 1 g = c.toFun g
  rw [c.iCycles_toCocycle]
  change c.toFun g - c.toFun 1 = c.toFun g
  rw [c.map_one, sub_zero]

end ContinuousCohomology
