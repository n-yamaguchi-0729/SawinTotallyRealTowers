/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterKernel
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingPrincipalInertiaCriterion
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingHilbertRamificationComparison
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteRamificationPrimary
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.Core

/-!
# The actual ring-character wild kernel is primary

The ring predicate is first put in actual ideal inertia. The native Hilbert
predicate comparison then supplies the ramification element and its p-power
order. The final ring-kernel scope consumes this proved order statement and
does not simultaneously open the two Hilbert subgroup types.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

private theorem principalUnitMultipliers_mem_inertia
    (R : Type u) [CommRing R] [IsLocalRing R]
    (G : Type v) [Group G] [MulSemiringAction G R] (σ : G)
    (hσ : ∀ x : R, ∃ a : Rˣ,
      σ • x = x * (a : R) ∧ (a : R) - 1 ∈ IsLocalRing.maximalIdeal R) :
    σ ∈ (IsLocalRing.maximalIdeal R).inertia G := by
  intro x
  obtain ⟨a, ha, hprincipal⟩ := hσ x
  rw [ha, ← mul_sub_one]
  exact (IsLocalRing.maximalIdeal R).mul_mem_left x hprincipal

open _root_.RamificationTheory.HilbertRamification.ValuationSubring in
/-- A decomposition element acting by principal units has prime-power order in residue
characteristic `p`. -/
theorem principalUnitMultipliers_pow_prime_eq_one
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField V) p] [Finite (decompositionGroup K V)]
    (σ : decompositionGroup K V)
    (hσ : ∀ x : V, ∃ a : Vˣ,
      σ • x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) :
    ∃ n : ℕ, σ ^ (p ^ n) = 1 := by
  have hIeq : (IsLocalRing.maximalIdeal V).inertia (decompositionGroup K V) =
      inertiaGroup K V :=
    TameAbhyankar.SGA1.TameInertiaCyclicCore.valuationSubring_maximalIdeal_inertia_eq K V
  have hI : σ ∈ inertiaGroup K V := hIeq ▸
    principalUnitMultipliers_mem_inertia V (decompositionGroup K V) σ hσ
  let τ : inertiaGroup K V := ⟨σ, hI⟩
  have hτ : τ ∈ ramificationGroup K V :=
    (mem_ramificationGroup_iff_principalUnitMultipliers K V τ).mpr hσ
  obtain ⟨n, hn⟩ :=
    ramificationGroup_isPGroup_of_residueChar K V p ⟨τ, hτ⟩
  refine ⟨n, ?_⟩
  exact congrArg (fun t : ramificationGroup K V =>
    ((t : inertiaGroup K V) : decompositionGroup K V)) hn

open _root_.RamificationTheory.HilbertRamification.ValuationSubring in
/-- A decomposition element acting by principal units is trivial in residue characteristic zero. -/
theorem principalUnitMultipliers_eq_one_of_residueCharZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L)
    [CharZero (IsLocalRing.ResidueField V)] [Finite (decompositionGroup K V)]
    (σ : decompositionGroup K V)
    (hσ : ∀ x : V, ∃ a : Vˣ,
      σ • x = x * (a : V) ∧ (a : V) - 1 ∈ IsLocalRing.maximalIdeal V) : σ = 1 := by
  have hIeq : (IsLocalRing.maximalIdeal V).inertia (decompositionGroup K V) =
      inertiaGroup K V :=
    TameAbhyankar.SGA1.TameInertiaCyclicCore.valuationSubring_maximalIdeal_inertia_eq K V
  have hI : σ ∈ inertiaGroup K V := hIeq ▸
    principalUnitMultipliers_mem_inertia V (decompositionGroup K V) σ hσ
  let τ : inertiaGroup K V := ⟨σ, hI⟩
  have hτ : τ ∈ ramificationGroup K V :=
    (mem_ramificationGroup_iff_principalUnitMultipliers K V τ).mpr hσ
  rw [ramificationGroup_eq_bot_of_residueCharZero K V] at hτ
  exact congrArg (fun t : inertiaGroup K V => (t : decompositionGroup K V)) hτ

open _root_.RamificationTheory.HilbertRamification.ValuationSubring in
/-- The literal ring-character kernel for the native finite decomposition
action is a p-group. Actual Hilbert ramification supplies the p-power order. -/
theorem principalUnitInertia_isPGroup_of_residueChar
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField V) p]
    [Finite (decompositionGroup K V)] :
    IsPGroup p (principalUnitInertia V (decompositionGroup K V)) := by
  intro σ
  obtain ⟨n, hn⟩ := principalUnitMultipliers_pow_prime_eq_one K V p
    ((σ : (IsLocalRing.maximalIdeal V).inertia (decompositionGroup K V)) :
      decompositionGroup K V)
    ((mem_principalUnitInertia_iff_sub_one_mem V (decompositionGroup K V)
      (σ : (IsLocalRing.maximalIdeal V).inertia (decompositionGroup K V))).mp σ.property)
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hn

open _root_.RamificationTheory.HilbertRamification.ValuationSubring in
/-- In residue characteristic zero, the actual ring-character wild kernel
for a finite decomposition action is trivial. -/
theorem principalUnitInertia_eq_bot_of_residueCharZero
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (IsLocalRing.ResidueField V)] [Finite (decompositionGroup K V)] :
    principalUnitInertia V (decompositionGroup K V) = ⊥ := by
  apply bot_unique
  intro σ hσ
  apply Subtype.ext
  exact principalUnitMultipliers_eq_one_of_residueCharZero K V
    (σ : decompositionGroup K V)
    ((mem_principalUnitInertia_iff_sub_one_mem V (decompositionGroup K V) σ).mp hσ)

end RamificationTheory.HilbertRamification.DiscreteValuationRing
