/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingPrincipalWildPrimary
import Mathlib.RingTheory.Valuation.RamificationGroup

/-!
# Orders of field automorphisms acting by principal units

For a valuation ring with finite decomposition group, a compatible surjective ring map acting by
principal-unit multipliers gives a field automorphism of p-power order in positive residue
characteristic p. In residue characteristic zero, that automorphism is trivial.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open scoped Pointwise
open _root_.RamificationTheory.HilbertRamification.ValuationSubring

universe u v

private theorem mem_decomposition_of_surjective_ring_square
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (σ : L ≃ₐ[K] L) (τ : V →+* V) (hτ : Function.Surjective τ)
    (hfield : V.subtype.comp τ = σ.toRingHom.comp V.subtype) :
    σ ∈ decompositionGroup K V := by
  change σ • V = V
  apply SetLike.ext
  intro x
  rw [_root_.ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : (τ ⟨y, hy⟩ : L) = σ y := RingHom.congr_fun hfield ⟨y, hy⟩
    change σ y ∈ V
    exact h ▸ (τ ⟨y, hy⟩).property
  · intro hx
    obtain ⟨y, hy⟩ := hτ ⟨x, hx⟩
    refine ⟨(y : L), y.property, ?_⟩
    change σ (y : L) = x
    have h : (τ y : L) = σ (y : L) := RingHom.congr_fun hfield y
    exact h.symm.trans (congrArg (fun z : V => (z : L)) hy)

private theorem native_principalUnitMultipliers_of_ring_square
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (σ : decompositionGroup K V) (τ : V →+* V)
    (hfield : V.subtype.comp τ = (σ : L ≃ₐ[K] L).toRingHom.comp V.subtype)
    (hprincipal : ∀ x : V, ∃ a : Vˣ,
      τ x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) :
    ∀ x : V, ∃ a : Vˣ,
      σ • x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V := by
  intro x
  obtain ⟨a, ha, hunit⟩ := hprincipal x
  refine ⟨a, ?_, hunit⟩
  apply Subtype.ext
  have h : (τ x : L) = (σ : L ≃ₐ[K] L) (x : L) := RingHom.congr_fun hfield x
  exact h.symm.trans (congrArg (fun z : V => (z : L)) ha)

/-- The actual field automorphism has p-power order when its actual local
ring automorphism acts by principal units. The native decomposition element
and its Hilbert ramification membership are constructed from the square. -/
theorem fieldAutomorphism_pow_prime_eq_one_of_local_principal_units
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField V) p] [Finite (decompositionGroup K V)]
    (σ : L ≃ₐ[K] L) (τ : V →+* V) (hτ : Function.Surjective τ)
    (hfield : V.subtype.comp τ = σ.toRingHom.comp V.subtype)
    (hprincipal : ∀ x : V, ∃ a : Vˣ,
      τ x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) :
    ∃ n : ℕ, σ ^ (p ^ n) = 1 := by
  have hD : σ ∈ decompositionGroup K V :=
    mem_decomposition_of_surjective_ring_square K V σ τ hτ hfield
  let δ : decompositionGroup K V := ⟨σ, hD⟩
  have hδ := native_principalUnitMultipliers_of_ring_square K V δ τ
    hfield hprincipal
  clear hprincipal hfield hτ τ
  obtain ⟨n, hn⟩ := principalUnitMultipliers_pow_prime_eq_one K V p δ hδ
  exact ⟨n, congrArg (fun g : decompositionGroup K V => (g : L ≃ₐ[K] L)) hn⟩

/-- The actual field automorphism is trivial in residue characteristic zero
when its actual local ring automorphism acts by principal units. -/
theorem fieldAutomorphism_eq_one_of_local_principal_units_charZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L)
    [CharZero (IsLocalRing.ResidueField V)] [Finite (decompositionGroup K V)]
    (σ : L ≃ₐ[K] L) (τ : V →+* V) (hτ : Function.Surjective τ)
    (hfield : V.subtype.comp τ = σ.toRingHom.comp V.subtype)
    (hprincipal : ∀ x : V, ∃ a : Vˣ,
      τ x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) : σ = 1 := by
  have hD : σ ∈ decompositionGroup K V :=
    mem_decomposition_of_surjective_ring_square K V σ τ hτ hfield
  let δ : decompositionGroup K V := ⟨σ, hD⟩
  have hδ := native_principalUnitMultipliers_of_ring_square K V δ τ
    hfield hprincipal
  clear hprincipal hfield hτ τ
  exact congrArg (fun g : decompositionGroup K V => (g : L ≃ₐ[K] L))
    (principalUnitMultipliers_eq_one_of_residueCharZero K V δ hδ)

end RamificationTheory.HilbertRamification.DiscreteValuationRing
