/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Noetherian.Basic

/-!
Deduce module finiteness from a kernel contained in a range over a Noetherian ring.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Module_Finite_of_ker_le_range_of_isNoetherianRing

theorem _root_.Module.Finite.of_ker_le_range_of_isNoetherianRing {R : Type*} [CommRing R]
    [IsNoetherianRing R] {M N₁ N₂ : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [Module.Finite R N₁]
      [Module.Finite R N₂]
    (α : N₁ →ₗ[R] M) (β : M →ₗ[R] N₂) (h : LinearMap.ker β ≤ LinearMap.range α) : Module.Finite
      R M := by
  have hN₁ : Module.Finite R N₁ := inferInstance
  have hN₂ : Module.Finite R N₂ := inferInstance
  have : IsNoetherian R (LinearMap.range α) :=
    isNoetherian_of_fg_of_noetherian _ (LinearMap.range_eq_map α ▸ (Module.finite_def.mp hN₁).map _)
  have : IsNoetherian R N₂ := isNoetherian_of_isNoetherianRing_of_finite R N₂
  refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker β ?_ ?_⟩
  · rw [Submodule.map_top]; exact IsNoetherian.noetherian _
  · rw [top_inf_eq]
    have hcomap : ((LinearMap.ker β).comap (LinearMap.range α).subtype).FG :=
      IsNoetherian.noetherian _
    have hmap := hcomap.map (LinearMap.range α).subtype
    rwa [Submodule.map_comap_subtype, inf_eq_right.mpr h] at hmap
end Module_Finite_of_ker_le_range_of_isNoetherianRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
