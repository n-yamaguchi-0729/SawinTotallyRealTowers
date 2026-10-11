/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.FieldTheory.KrullTopology
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Transport of Galois groups between equivalent extension fields

A base-linear field equivalence conjugates the relative Galois groups and
preserves their Krull topologies. A finite intermediate field pulls back to a
finite intermediate field under the inverse equivalence, so no algebraicity
assumption on the ambient extensions is needed.
-/

namespace KummerTheory

open scoped Topology

variable {K Ω Ω' : Type*} [Field K] [Field Ω] [Field Ω']
  [Algebra K Ω] [Algebra K Ω']

/-- Conjugation by an algebra equivalence is continuous for the Krull
topologies on the relative Galois groups. -/
theorem galoisClosureTransport_continuous (e : Ω ≃ₐ[K] Ω') :
    Continuous (AlgEquiv.autCongr e) := by
  apply continuous_of_tendsto_nhds_one (AlgEquiv.autCongr e)
  rw [Filter.tendsto_def]
  intro U hU
  obtain ⟨E, hE, hEU⟩ := (krullTopology_mem_nhds_one_iff K Ω' U).mp hU
  let F : IntermediateField K Ω := E.map e.symm.toAlgHom
  have hF : FiniteDimensional K F :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap E e.symm.toAlgHom).toLinearEquiv
  apply (krullTopology_mem_nhds_one_iff K Ω ((AlgEquiv.autCongr e) ⁻¹' U)).mpr
  refine ⟨F, hF, ?_⟩
  intro σ hσ
  apply hEU
  apply (IntermediateField.mem_fixingSubgroup_iff E (AlgEquiv.autCongr e σ)).mpr
  intro x hx
  have hxF : e.symm x ∈ F := ⟨x, hx, rfl⟩
  have hfix : σ (e.symm x) = e.symm x :=
    (IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ (e.symm x) hxF
  change e (σ (e.symm x)) = x
  rw [hfix, e.apply_symm_apply]

/-- A base-linear field equivalence transports relative Galois groups as
topological groups with the Krull topology. -/
def galoisClosureTransport (e : Ω ≃ₐ[K] Ω') : Gal(Ω/K) ≃ₜ* Gal(Ω'/K) where
  toMulEquiv := AlgEquiv.autCongr e
  continuous_toFun := galoisClosureTransport_continuous e
  continuous_invFun := galoisClosureTransport_continuous e.symm

/-- Forgetting topology recovers the algebraic conjugation equivalence. -/
theorem galoisClosureTransport_toMulEquiv (e : Ω ≃ₐ[K] Ω') :
    (galoisClosureTransport e).toMulEquiv = AlgEquiv.autCongr e := by
  rfl

/-- The transported automorphism evaluates by conjugating in the extension fields. -/
theorem galoisClosureTransport_apply (e : Ω ≃ₐ[K] Ω') (σ : Gal(Ω/K)) (x : Ω') :
    galoisClosureTransport e σ x = e (σ (e.symm x)) := by
  rfl

/-- The inverse transport evaluates by the inverse field equivalence. -/
theorem galoisClosureTransport_symm_apply (e : Ω ≃ₐ[K] Ω')
    (σ : Gal(Ω'/K)) (x : Ω) :
    (galoisClosureTransport e).symm σ x = e.symm (σ (e x)) := by
  rfl

/-- Transport in the reverse direction is transport by the inverse algebra equivalence. -/
theorem galoisClosureTransport_symm (e : Ω ≃ₐ[K] Ω') :
    (galoisClosureTransport e).symm = galoisClosureTransport e.symm := by
  apply ContinuousMulEquiv.ext
  intro σ
  apply AlgEquiv.ext
  intro x
  rw [galoisClosureTransport_symm_apply, galoisClosureTransport_apply,
    AlgEquiv.symm_symm]

end KummerTheory
