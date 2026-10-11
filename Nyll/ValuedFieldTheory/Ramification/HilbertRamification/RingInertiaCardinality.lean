/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Cardinality factorization for DVR inertia

Proves that the cardinality of inertia is the tame image order multiplied by the cardinality of
principal-unit inertia.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

private theorem card_eq_range_card_mul_ker_card
    {M : Type u} {N : Type v} [Group M] [Group N] (f : M →* N) :
    Nat.card M = Nat.card f.range * Nat.card f.ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (G : Type v) [Group G] [MulSemiringAction G R]

/-- The actual inertia order factors into the actual tame image order and
the actual principal-unit kernel order, without exposing a second quotient type. -/
theorem inertia_card_eq_tameOrder_mul_principalUnitInertia_card :
    Nat.card ((IsLocalRing.maximalIdeal R).inertia G) =
      tameOrder R G * Nat.card (principalUnitInertia R G) := by
  rw [principalUnitInertia_eq_character_ker]
  exact card_eq_range_card_mul_ker_card (inertiaResidueCharacter R G)

end RamificationTheory.HilbertRamification.DiscreteValuationRing
