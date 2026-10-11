/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic.Ring

/-!
# Additive Hilbert 90 for continuous Galois cocycles

In a finite Galois extension, an element of trace one gives an explicit
coboundary. A locally constant cocycle on an infinite Galois group descends
to a finite Galois field, so the same construction applies.
-/

namespace GaloisCohomology
open scoped Topology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

/-- An additive cocycle on a finite Galois extension is a coboundary. -/
theorem additiveHilbert90_finite [FiniteDimensional K Ω]
    (c : Gal(Ω/K) → Ω)
    (hc : ∀ σ τ : Gal(Ω/K), c (σ * τ) = σ (c τ) + c σ) :
    ∃ β : Ω, ∀ σ : Gal(Ω/K), σ β - β = c σ := by
  classical
  obtain ⟨a, ha⟩ := Algebra.trace_surjective K Ω 1
  have htrace : ∑ τ : Gal(Ω/K), τ a = 1 := by
    rw [← trace_eq_sum_automorphisms, ha, map_one]
  let B : Ω := ∑ τ : Gal(Ω/K), c τ * τ a
  have hB (σ : Gal(Ω/K)) : σ B = B - c σ := by
    have hperm : (∑ τ : Gal(Ω/K), c (σ * τ) * (σ * τ) a) = B :=
      Fintype.sum_bijective (fun τ : Gal(Ω/K) => σ * τ)
        (Group.mulLeft_bijective σ) _ _ (fun _ => rfl)
    have hpermTrace : (∑ τ : Gal(Ω/K), (σ * τ) a) = 1 := by
      rw [Fintype.sum_bijective (fun τ : Gal(Ω/K) => σ * τ)
        (Group.mulLeft_bijective σ) _ (fun τ => τ a) (fun _ => rfl)]
      exact htrace
    calc
      σ B = ∑ τ : Gal(Ω/K), (c (σ * τ) - c σ) * (σ * τ) a := by
        dsimp only [B]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro τ _
        rw [map_mul, hc, add_sub_cancel_right]
        rfl
      _ = (∑ τ : Gal(Ω/K), c (σ * τ) * (σ * τ) a) -
          c σ * (∑ τ : Gal(Ω/K), (σ * τ) a) := by
        simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = B - c σ := by rw [hperm, hpermTrace, mul_one]
  refine ⟨-B, ?_⟩
  intro σ
  rw [map_neg, hB]
  ring

private theorem additive_cocycle_finite_stage
    (c : Gal(Ω/K) → Ω)
    (hc : ∀ σ τ : Gal(Ω/K), c (σ * τ) = σ (c τ) + c σ)
    (hlc : IsLocallyConstant c) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (cE : Gal(E/K) → E),
      (∀ σ τ : Gal(E/K), cE (σ * τ) = σ (cE τ) + cE σ) ∧
      ∀ σ : Gal(Ω/K), (cE (AlgEquiv.restrictNormalHom E σ) : Ω) = c σ := by
  classical
  have hc1 : c 1 = 0 := by
    have h : c 1 = c 1 + c 1 := hc 1 1
    exact (add_left_cancel ((add_zero (c 1)).trans h)).symm
  have hnhds : {g : Gal(Ω/K) | c g = 0} ∈ 𝓝 1 :=
    (hlc.isOpen_fiber 0).mem_nhds hc1
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := K) (K := Ω) {g : Gal(Ω/K) | c g = 0}).1 hnhds
  let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  have hker (σ : Gal(Ω/K)) (hσ : r σ = 1) : c σ = 0 := by
    apply hE
    change σ ∈ E.fixingSubgroup
    rw [← IntermediateField.restrictNormalHom_ker]
    exact hσ
  have hfactor (σ τ : Gal(Ω/K)) (heq : r σ = r τ) : c σ = c τ := by
    have hrel : r (τ⁻¹ * σ) = 1 := by rw [map_mul, map_inv, heq, inv_mul_cancel]
    have hc_rel := hker (τ⁻¹ * σ) hrel
    calc
      c σ = c (τ * (τ⁻¹ * σ)) := by rw [← mul_assoc, mul_inv_cancel, one_mul]
      _ = c τ := by rw [hc, hc_rel, map_zero, zero_add]
  have hmem (σ : Gal(Ω/K)) : c σ ∈ E.toIntermediateField := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E.toIntermediateField,
      IntermediateField.mem_fixedField_iff]
    intro τ hτ
    have hrτ : r τ = 1 := by
      change τ ∈ r.ker
      rw [IntermediateField.restrictNormalHom_ker]
      exact hτ
    have hcτ : c τ = 0 := hker τ hrτ
    calc
      τ (c σ) = c (τ * σ) := by rw [hc, hcτ, add_zero]
      _ = c σ := hfactor (τ * σ) σ (by rw [map_mul, hrτ, one_mul])
  let cE : Gal(E/K) → E := fun σ => ⟨c (hr σ).choose, hmem (hr σ).choose⟩
  have hvalue (σ : Gal(Ω/K)) : (cE (r σ) : Ω) = c σ := by
    exact hfactor _ _ (hr (r σ)).choose_spec
  have hcE (σ τ : Gal(E/K)) : cE (σ * τ) = σ (cE τ) + cE σ := by
    obtain ⟨σ', rfl⟩ := hr σ
    obtain ⟨τ', rfl⟩ := hr τ
    apply Subtype.ext
    change (cE (r σ' * r τ') : Ω) =
      ((r σ') (cE (r τ')) : Ω) + (cE (r σ') : Ω)
    rw [← map_mul, hvalue,
      AlgEquiv.restrictNormalHom_apply E.toIntermediateField σ' (cE (r τ'))]
    rw [hvalue, hvalue]
    exact hc σ' τ'
  exact ⟨E, cE, hcE, hvalue⟩

/-- Locally constant additive cocycles are coboundaries in any Galois extension. -/
theorem additiveHilbert90_of_isLocallyConstant
    (c : Gal(Ω/K) → Ω)
    (hc : ∀ σ τ : Gal(Ω/K), c (σ * τ) = σ (c τ) + c σ)
    (hlc : IsLocallyConstant c) :
    ∃ β : Ω, ∀ σ : Gal(Ω/K), σ β - β = c σ := by
  obtain ⟨E, cE, hcE, hvalue⟩ := additive_cocycle_finite_stage c hc hlc
  obtain ⟨β, hβ⟩ := additiveHilbert90_finite cE hcE
  refine ⟨(β : Ω), ?_⟩
  intro σ
  have h := congrArg (fun x : E => (x : Ω)) (hβ (AlgEquiv.restrictNormalHom E σ))
  change ((AlgEquiv.restrictNormalHom E σ) β : Ω) - (β : Ω) =
    (cE (AlgEquiv.restrictNormalHom E σ) : Ω) at h
  rw [AlgEquiv.restrictNormalHom_apply, hvalue] at h
  exact h

end GaloisCohomology
