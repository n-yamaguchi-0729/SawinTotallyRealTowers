/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProP.GeneratorRank
import Nyll.ProCGroups.ProP.H1PowerCommutator
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Generator rank as continuous `H¹` dimension

This file identifies continuous trivial-coefficient degree-one classes with
the linear dual of the power--commutator quotient.  For a finitely generated
pro-`p` group the quotient is finite, so continuity is automatic and P06 gives
the generator-rank formula.
-/

open scoped Topology IsMulCommutative

namespace ClassFieldTower.ProP

universe u

variable {p : ℕ} {G : Type u}
variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

local instance : TopologicalSpace (ZMod p) := ⊥
local instance : DiscreteTopology (ZMod p) := discreteTopology_bot _
local instance : (closedPowerCommutator p G).Normal :=
  closedPowerCommutator_normal p G
local instance : IsMulCommutative (powerCommutatorQuotient p G) :=
  powerCommutatorQuotient_isMulCommutative p G
local instance : Module (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
  AddCommGroup.zmodModule fun x => by
    change (Additive.toMul x) ^ p = 1
    exact powerCommutatorQuotient_pow_eq_one p G (Additive.toMul x)
local instance : Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

/-- The continuous part of the algebraic dual of the power--commutator quotient. -/
def continuousPowerCommutatorDual :
    Submodule (ZMod p)
      (Module.Dual (ZMod p) (Additive (powerCommutatorQuotient p G))) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_const
  add_mem' hf hg := hf.add hg
  smul_mem' c f hf := by
    change Continuous fun x => c * f x
    exact continuous_const.mul hf

/-- Turn a quotient degree-one class into its underlying continuous linear functional. -/
def quotientH1ToContinuousDual
    (f : ContinuousH1ZMod (p := p)
      (G := powerCommutatorQuotient p G)) :
    continuousPowerCommutatorDual (p := p) (G := G) :=
  ⟨f.toAddMonoidHom.toZModLinearMap p, f.continuous_toFun⟩

/-- Equip a continuous linear functional with its continuous additive-hom structure. -/
def quotientH1OfContinuousDual
    (f : continuousPowerCommutatorDual (p := p) (G := G)) :
    ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G) where
  toAddMonoidHom := f.1.toAddMonoidHom
  continuous_toFun := f.2

/-- Quotient degree-one classes are exactly the continuous linear dual. -/
def quotientH1ContinuousDualLinearEquiv :
    ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G) ≃ₗ[ZMod p]
      continuousPowerCommutatorDual (p := p) (G := G) where
  toFun := quotientH1ToContinuousDual
  invFun := quotientH1OfContinuousDual
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl
  map_add' f g := by ext x; rfl
  map_smul' c f := by
    ext x
    let ev : ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G) →+
        ZMod p :=
      { toFun := fun h => h x
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact ZMod.map_smul ev c f

/-- Continuous `H¹` is the continuous dual of the elementary quotient. -/
def continuousH1PowerCommutatorDualEquiv :
    ContinuousH1ZMod (p := p) (G := G) ≃ₗ[ZMod p]
      continuousPowerCommutatorDual (p := p) (G := G) :=
  (h1PowerCommutatorQuotientLinearEquiv (p := p) (G := G)).trans
    (quotientH1ContinuousDualLinearEquiv (p := p) (G := G))

theorem continuousPowerCommutatorDual_eq_top
    [DiscreteTopology (powerCommutatorQuotient p G)] :
    continuousPowerCommutatorDual (p := p) (G := G) = ⊤ := by
  apply top_unique
  intro f _
  exact continuous_of_discreteTopology

/-- For a discrete elementary quotient, continuous `H¹` is the full algebraic dual. -/
def continuousH1PowerCommutatorFullDualLinearEquiv
    [DiscreteTopology (powerCommutatorQuotient p G)] :
    ContinuousH1ZMod (p := p) (G := G) ≃ₗ[ZMod p]
      Module.Dual (ZMod p) (Additive (powerCommutatorQuotient p G)) :=
  (continuousH1PowerCommutatorDualEquiv (p := p) (G := G)).trans
    (LinearEquiv.ofTop (continuousPowerCommutatorDual (p := p) (G := G))
      (continuousPowerCommutatorDual_eq_top (p := p) (G := G)))

theorem finrank_continuousH1_eq_finrank_powerCommutatorQuotient
    [Fact p.Prime] [DiscreteTopology (powerCommutatorQuotient p G)] :
    Module.finrank (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) =
      Module.finrank (ZMod p) (Additive (powerCommutatorQuotient p G)) := by
  rw [(continuousH1PowerCommutatorFullDualLinearEquiv
    (p := p) (G := G)).finrank_eq, Subspace.dual_finrank_eq]

section Profinite

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [Fact p.Prime]

local instance : IsClosed (closedPowerCommutator p G : Set G) :=
  isClosed_closedPowerCommutator p G

/-- For a finitely generated pro-`p` group, generator rank equals the dimension
of continuous trivial-coefficient degree-one cohomology. -/
theorem topologicalGeneratorRank_eq_finrank_continuousH1
    (hpG : ProCGroups.ProC.HasPGroupOpenNormalBasis p G)
    (hfg : ProCGroups.FiniteGeneration.TopologicallyFinitelyGenerated G) :
    topologicalGeneratorRank G =
      Module.finrank (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) := by
  let _ : Finite (powerCommutatorQuotient p G) :=
    powerCommutatorQuotient_finite_of_topologicallyFinitelyGenerated hfg
  rw [topologicalGeneratorRank_eq_powerCommutatorQuotient_finrank hpG hfg]
  exact (finrank_continuousH1_eq_finrank_powerCommutatorQuotient
    (p := p) (G := G)).symm

end Profinite

end ClassFieldTower.ProP
