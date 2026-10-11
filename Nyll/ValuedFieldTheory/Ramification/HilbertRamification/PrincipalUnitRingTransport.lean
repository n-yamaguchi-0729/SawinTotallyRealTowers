/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Ring.Equiv

/-!
# Transport of principal-unit multipliers

Proves that the principal-unit multiplier condition is preserved, in both directions, by a
local-ring equivalence intertwining the ring maps.
-/

namespace RamificationTheory.HilbertRamification.LocalRing

open IsLocalRing

universe u v

/-- Transport the actual principal-unit multiplier predicate using only the
maximal ideals and the actual coefficient square; no residue field is opened. -/
theorem principalUnitMultipliers_transport
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (σ : R →+* R) (τ : S →+* S)
    (hcomm : e.toRingHom.comp σ = τ.comp e.toRingHom)
    (hσ : ∀ x : R, ∃ a : Rˣ, σ x = x * (a : R) ∧ (a : R) - 1 ∈ maximalIdeal R) :
    ∀ y : S, ∃ a : Sˣ, τ y = y * (a : S) ∧ (a : S) - 1 ∈ maximalIdeal S := by
  intro y
  let x := e.symm y
  have hx : e x = y := e.apply_symm_apply y
  obtain ⟨a, ha, hprincipal⟩ := hσ x
  refine ⟨Units.map e.toMonoidHom a, ?_, ?_⟩
  · calc
      τ y = τ (e x) := congrArg τ hx.symm
      _ = e (σ x) := (RingHom.congr_fun hcomm x).symm
      _ = e x * e (a : R) := by rw [ha, map_mul]
      _ = _ := by rw [hx]; rfl
  · have h := (IsLocalRing.map_ringEquiv_maximalIdeal e).le
      (Ideal.mem_map_of_mem e.toRingHom hprincipal)
    rw [map_sub, map_one] at h
    exact h

/-- The same actual principal-unit predicate is invariant under ring/action
comparison; the reverse coefficient square is derived. -/
theorem principalUnitMultipliers_iff_of_ringEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (σ : R →+* R) (τ : S →+* S)
    (hcomm : e.toRingHom.comp σ = τ.comp e.toRingHom) :
    (∀ x : R, ∃ a : Rˣ, σ x = x * (a : R) ∧ (a : R) - 1 ∈ maximalIdeal R) ↔
      ∀ y : S, ∃ a : Sˣ, τ y = y * (a : S) ∧ (a : S) - 1 ∈ maximalIdeal S := by
  constructor
  · exact principalUnitMultipliers_transport e σ τ hcomm
  · intro hτ
    have hrev : e.symm.toRingHom.comp τ = σ.comp e.symm.toRingHom := by
      apply RingHom.ext
      intro y
      apply e.injective
      change e (e.symm (τ y)) = e (σ (e.symm y))
      rw [e.apply_symm_apply]
      have h := RingHom.congr_fun hcomm (e.symm y)
      change e (σ (e.symm y)) = τ (e (e.symm y)) at h
      rw [e.apply_symm_apply] at h
      exact h.symm
    exact principalUnitMultipliers_transport e.symm τ σ hrev hτ

end RamificationTheory.HilbertRamification.LocalRing
