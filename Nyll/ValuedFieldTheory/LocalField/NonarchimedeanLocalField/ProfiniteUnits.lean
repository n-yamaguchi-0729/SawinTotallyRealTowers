/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Group.Units

/-!
# Profinite valuation-ring units

The topology of a nonarchimedean local field is Hausdorff and totally disconnected because
valuation balls are clopen. This file records those structures as named results, without
registering additional global instances, and packages the valuation-ring unit group as a
profinite group.
-/



@[expose] public section

noncomputable section

universe u

namespace LocalFieldTheory

open scoped ValuativeRel

/-- A nonarchimedean local field is Hausdorff for its valuative topology. -/
theorem localFieldT2Space
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] : T2Space K := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  let r := (ValuativeRel.valuation K).restrict x
  refine ⟨{y : K | (ValuativeRel.valuation K).restrict y < r}, ?_, ?_⟩
  · exact ((ValuativeRel.valuation K).isOpen_ball r).mem_nhds
      (by
        change (ValuativeRel.valuation K).restrict 0 < (ValuativeRel.valuation K).restrict x
        rw [map_zero, zero_lt_iff]
        exact (Valuation.ne_zero_iff (ValuativeRel.valuation K).restrict).2 hx)
  · exact lt_irrefl r

/-- Distinct points of a nonarchimedean local field are separated by a clopen valuation ball. -/
theorem localFieldTotallySeparatedSpace
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : TotallySeparatedSpace K := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  let r := (ValuativeRel.valuation K).restrict (y - x)
  refine ⟨{z : K | (ValuativeRel.valuation K).restrict (z - x) < r}, ?_, ?_, ?_⟩
  · change IsClopen
      ((fun z : K => z - x) ⁻¹'
        {w : K | (ValuativeRel.valuation K).restrict w < r})
    exact ((ValuativeRel.valuation K).isClopen_ball r).preimage
      (continuous_id.sub continuous_const)
  · have hyx : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
    change (ValuativeRel.valuation K).restrict (x - x) <
      (ValuativeRel.valuation K).restrict (y - x)
    rw [sub_self, map_zero, zero_lt_iff]
    exact (Valuation.ne_zero_iff (ValuativeRel.valuation K).restrict).2 hyx
  · exact lt_irrefl r

/-- A nonarchimedean local field is totally disconnected for its valuative topology. -/
theorem localFieldTotallyDisconnectedSpace
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : TotallyDisconnectedSpace K := by
  let : TotallySeparatedSpace K := localFieldTotallySeparatedSpace K
  infer_instance

/-- The unit group of the valuation ring of a nonarchimedean local field, as a profinite group. -/
noncomputable def localUnits_profinite
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : ProfiniteGrp := by
  letI : T2Space K := localFieldT2Space K
  letI : TotallyDisconnectedSpace K := localFieldTotallyDisconnectedSpace K
  letI : TotallyDisconnectedSpace (𝒪[K])ᵐᵒᵖ :=
    Homeomorph.totallyDisconnectedSpace
      (MulOpposite.opHomeomorph : 𝒪[K] ≃ₜ (𝒪[K])ᵐᵒᵖ)
  letI : TotallyDisconnectedSpace 𝒪[K]ˣ := by
    rw [← (Units.isEmbedding_embedProduct (M := 𝒪[K])).isTotallyDisconnected_range]
    exact isTotallyDisconnected_of_totallyDisconnectedSpace _
  exact ProfiniteGrp.of 𝒪[K]ˣ

end LocalFieldTheory
