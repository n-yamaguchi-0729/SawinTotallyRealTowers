/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterKernel
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# A maximal-ideal criterion for principal-unit inertia

Expresses membership in principal-unit inertia by requiring each multiplier minus one to lie in
the maximal ideal.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

private theorem residue_eq_one_iff_sub_one_mem
    {R : Type u} [CommRing R] [IsLocalRing R] (x : R) :
    residue R x = 1 ↔ x - 1 ∈ maximalIdeal R := by
  rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]

/-- Membership in the same actual principal-unit inertia is expressed without
opening the residue field at downstream comparison boundaries. -/
theorem mem_principalUnitInertia_iff_sub_one_mem
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Type v) [Group G] [MulSemiringAction G R]
    (σ : (maximalIdeal R).inertia G) :
    σ ∈ principalUnitInertia R G ↔
      ∀ x : R, ∃ a : Rˣ,
        (σ : G) • x = x * (a : R) ∧ (a : R) - 1 ∈ maximalIdeal R := by
  change (∀ x : R, ∃ a : Rˣ,
    (σ : G) • x = x * (a : R) ∧ residue R (a : R) = 1) ↔ _
  simp only [residue_eq_one_iff_sub_one_mem]

end RamificationTheory.HilbertRamification.DiscreteValuationRing
