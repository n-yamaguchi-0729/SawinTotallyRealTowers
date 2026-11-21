/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
public import Nyll.ClassFieldTheory.Definitions.LocalClassFieldTheory.OpenFiniteIndexSubgroup
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Open finite-index subgroups under a small field equivalence

The topological field equivalence between `K` and its small representative
induces an order equivalence between their open finite-index subgroups of
units.
-/

@[expose] public section

noncomputable section

namespace LocalFieldTheory

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The multiplicative groups of a local field and its small representative
are topologically isomorphic. -/
def shrinkUnitsContinuousMulEquiv :
    let : Small.{0} K := nonarchimedeanLocalField_small K
    (Shrink.{0} K)ˣ ≃ₜ* Kˣ := by
  intro sharedOwner1
  let h : Shrink.{0} K ≃ₜ K := (Shrink.homeomorph K).symm
  exact Units.mapContinuousMulEquiv {
    toMulEquiv := (Shrink.ringEquiv K).toMulEquiv
    continuous_toFun := h.continuous
    continuous_invFun := h.symm.continuous
  }

/-- Open finite-index subgroups correspond along the topological group
equivalence of unit groups. -/
def shrinkOpenFiniteIndexOrderIso :
    let : Small.{0} K := nonarchimedeanLocalField_small K
    ClassFieldTheory.OpenFiniteIndexSubgroup (Shrink.{0} K) ≃o
      ClassFieldTheory.OpenFiniteIndexSubgroup K := by
  intro sharedOwner1
  exact OpenFiniteIndexGroupSubgroup.map (shrinkUnitsContinuousMulEquiv K)

end LocalFieldTheory
