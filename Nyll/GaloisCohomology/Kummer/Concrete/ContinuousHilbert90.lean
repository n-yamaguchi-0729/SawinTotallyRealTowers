/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Noether Hilbert 90 for an infinite Galois extension

A locally constant multiplicative cocycle descends to a finite Galois stage.
An open normal subgroup in its identity fiber fixes every cocycle value, so the
finite-stage cocycle takes values in that actual intermediate field. Finite
Noether Hilbert 90 then produces a coboundary in the original extension.
-/

namespace KummerTheory
open scoped Topology
open groupCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

private theorem cocycle_finite_stage
    (c : Gal(Ω/K) → Ωˣ) (hc : IsMulCocycle₁ c)
    (hlc : IsLocallyConstant c) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (cE : Gal(E/K) → Eˣ),
      IsMulCocycle₁ cE ∧
      ∀ σ : Gal(Ω/K),
        ((cE (AlgEquiv.restrictNormalHom E σ) : E) : Ω) = (c σ : Ω) := by
  classical
  have hc1 : c 1 = 1 := map_one_of_isMulCocycle₁ hc
  have hnhds : {g : Gal(Ω/K) | c g = 1} ∈ 𝓝 1 :=
    (hlc.isOpen_fiber 1).mem_nhds hc1
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := K) (K := Ω) {g : Gal(Ω/K) | c g = 1}).1 hnhds
  let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  have hker (σ : Gal(Ω/K)) (hσ : r σ = 1) : c σ = 1 := by
    apply hE
    change σ ∈ E.fixingSubgroup
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hσ
  have hfactor (σ τ : Gal(Ω/K)) (heq : r σ = r τ) : c σ = c τ := by
    have hrel : r (τ⁻¹ * σ) = 1 := by rw [map_mul, map_inv, heq, inv_mul_cancel]
    have hc_rel := hker (τ⁻¹ * σ) hrel
    calc
      c σ = c (τ * (τ⁻¹ * σ)) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = c τ := by rw [hc, hc_rel, smul_one, one_mul]
  have hmem (σ : Gal(Ω/K)) : (c σ : Ω) ∈ E.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hrτ : r τ = 1 := by
      change τ ∈ r.ker
      rw [IntermediateField.restrictNormalHom_ker]
      exact hτ
    have hcτ : c τ = 1 := hker τ hrτ
    have hfixed : τ • c σ = c σ := by
      calc
        τ • c σ = c (τ * σ) := by rw [hc, hcτ, mul_one]
        _ = c σ := hfactor (τ * σ) σ (by rw [map_mul, hrτ, one_mul])
    exact congrArg (fun z : Ωˣ => (z : Ω)) hfixed
  let cE : Gal(E/K) → Eˣ := fun σ =>
    Units.mk0 ⟨(c (hr σ).choose : Ω), hmem (hr σ).choose⟩
      (fun h => Units.ne_zero (c (hr σ).choose) (congrArg Subtype.val h))
  have hvalue (σ : Gal(Ω/K)) :
      ((cE (r σ) : E) : Ω) = (c σ : Ω) := by
    change (c ((hr (r σ)).choose) : Ω) = (c σ : Ω)
    exact congrArg Units.val (hfactor _ _ (hr (r σ)).choose_spec)
  have hcE : IsMulCocycle₁ cE := by
    intro σ τ
    obtain ⟨σ', rfl⟩ := hr σ
    obtain ⟨τ', rfl⟩ := hr τ
    apply Units.ext
    apply Subtype.ext
    change ((cE (r σ' * r τ') : E) : Ω) =
      (r σ') (cE (r τ') : E) * (cE (r σ') : E)
    rw [← map_mul, hvalue,
      show ((r σ') (cE (r τ') : E) : Ω) = σ' ((cE (r τ') : E) : Ω) from
        AlgEquiv.restrictNormalHom_apply E.toIntermediateField σ' (cE (r τ') : E)]
    rw [hvalue, hvalue]
    exact congrArg Units.val (hc σ' τ')
  exact ⟨E, cE, hcE, hvalue⟩

/-- Continuous multiplicative cocycles into the discrete units of an arbitrary
Galois extension are coboundaries. -/
theorem noetherHilbert90_of_isLocallyConstant
    (c : Gal(Ω/K) → Ωˣ) (hc : IsMulCocycle₁ c)
    (hlc : IsLocallyConstant c) :
    IsMulCoboundary₁ c := by
  classical
  obtain ⟨E, cE, hcE, hvalue⟩ := cocycle_finite_stage c hc hlc
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units cE hcE
  refine ⟨Units.map (algebraMap E Ω).toMonoidHom β, ?_⟩
  intro σ
  apply Units.ext
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map,
    MonoidHom.coe_ofClass]
  change σ (algebraMap E Ω (β : E)) / algebraMap E Ω (β : E) = (c σ : Ω)
  rw [← hvalue σ]
  have hβ' : (AlgEquiv.restrictNormalHom E σ) (β : E) / (β : E) =
      (cE (AlgEquiv.restrictNormalHom E σ) : E) := by
    simpa only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map,
      MonoidHom.coe_ofClass] using congrArg Units.val (hβ (AlgEquiv.restrictNormalHom E σ))
  have h := congrArg (algebraMap E Ω) hβ'
  rw [map_div₀] at h
  change ((AlgEquiv.restrictNormalHom E σ) (β : E) : Ω) / ((β : E) : Ω) =
    ((cE (AlgEquiv.restrictNormalHom E σ) : E) : Ω) at h
  rw [AlgEquiv.restrictNormalHom_apply] at h
  exact h

end KummerTheory
