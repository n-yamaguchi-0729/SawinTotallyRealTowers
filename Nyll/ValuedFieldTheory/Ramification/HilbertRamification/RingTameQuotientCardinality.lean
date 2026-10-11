/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterKernel
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Tame image order as an inertia quotient cardinality

The first isomorphism theorem identifies the actual residue-character image
with inertia modulo the same principal-unit wild subgroup.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

/-- The actual tame image order is the cardinality of inertia modulo the
same principal-unit subgroup, by the first isomorphism theorem. -/
theorem tameOrder_eq_card_quotient_principalUnitInertia
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Type v) [Group G] [MulSemiringAction G R] :
    tameOrder R G = Nat.card
      ((IsLocalRing.maximalIdeal R).inertia G ⧸ principalUnitInertia R G) := by
  rw [principalUnitInertia_eq_character_ker]
  exact (Nat.card_congr
    (QuotientGroup.quotientKerEquivRange (inertiaResidueCharacter R G)).toEquiv).symm

end RamificationTheory.HilbertRamification.DiscreteValuationRing
