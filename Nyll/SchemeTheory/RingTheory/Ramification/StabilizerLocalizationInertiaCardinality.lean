/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Cardinality of localized inertia

Proves that the inertia group of the stabilizer action on a prime localization has the same
cardinality as the original ideal inertia group.
-/

open scoped Pointwise

namespace SchemeTheory

universe u v

/-- The actual local inertia used by the ring character has the original
ideal-inertia order. The comparison introduces no residue-field structure. -/
theorem stabilizerLocalization_inertia_card
    (B : Type u) [CommRing B] (G : Type v) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] :
    Nat.card ((IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia
      (MulAction.stabilizer G Q)) = Nat.card (Q.inertia G) := by
  rw [stabilizerLocalization_inertia_eq]
  exact Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (Q.inertia_le_stabilizer (M := G))).toEquiv

end SchemeTheory
