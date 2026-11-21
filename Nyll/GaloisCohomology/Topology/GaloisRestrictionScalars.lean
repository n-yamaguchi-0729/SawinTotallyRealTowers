/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Continuity of restriction of scalars on Galois groups

A finite subextension of the smaller base generates a finite subextension of
the larger base. Its fixing subgroup therefore supplies the required Krull
neighborhood, even when the larger base is transcendental over the smaller one.
-/

@[expose] public section

noncomputable section

open scoped Topology

namespace InfiniteGalois

variable (k K Ω : Type*) [Field k] [Field K] [Field Ω]
    [Algebra k K] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]

/-- Restriction of scalars is continuous for the actual Krull topologies. -/
theorem restrictScalarsHom_continuous :
    Continuous (AlgEquiv.restrictScalarsHom k : (Ω ≃ₐ[K] Ω) →* (Ω ≃ₐ[k] Ω)) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro N hN
  rw [map_one, krullTopology_mem_nhds_one_iff] at hN
  obtain ⟨E, hE, hN⟩ := hN
  have : FiniteDimensional k E := hE
  let F := IntermediateField.adjoin K (E : Set Ω)
  have : FiniteDimensional K F := Module.rank_lt_aleph0_iff.mp
    ((IntermediateField.adjoin_rank_le_of_isAlgebraic_right K E).trans_lt
      (Module.rank_lt_aleph0 k E))
  apply mem_nhds_iff.mpr
  refine ⟨F.fixingSubgroup, ?_, F.fixingSubgroup_isOpen, F.fixingSubgroup.one_mem⟩
  intro σ hσ
  apply hN
  simp only [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
  intro x hx
  exact hσ x (IntermediateField.subset_adjoin K (E : Set Ω) hx)

end InfiniteGalois
