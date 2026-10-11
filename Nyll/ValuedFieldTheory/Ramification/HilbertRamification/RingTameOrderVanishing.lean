/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingTameOrderRamification
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.OrderOfVanishing.Noetherian

/-!
# Tame-order divisibility of vanishing orders

Proves that the tame order divides the length-based order of vanishing of every nonzero fixed
element in a discrete valuation ring.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

/-- The actual tame order divides the native length-based order of every
actual nonzero fixed coefficient. The DVR valuation dictionary is confined
to this one-ring owner. -/
theorem tameOrder_dvd_ord_of_fixed
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]
    (x : R) (hx : x ≠ 0) (hfixed : ∀ g : G, g • x = x) :
    tameOrder R G ∣ (Ring.ord R x).toNat := by
  rw [Ring.ord_eq_addVal]
  exact tameOrder_dvd_addVal_of_fixed R G x hx hfixed

end RamificationTheory.HilbertRamification.DiscreteValuationRing
