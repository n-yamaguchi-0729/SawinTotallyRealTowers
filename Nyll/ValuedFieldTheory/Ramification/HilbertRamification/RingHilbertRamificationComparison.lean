/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.PrincipalUnitActionComparison
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ValuationSubring

/-!
# The ring-character wild predicate is actual Hilbert ramification

This consumer uses the native decomposition action on the actual valuation
subring. Both individual ring maps in the sparse comparison are supplied
by that action; their coefficient compatibility is definitional.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.ValuationSubring

universe u v

/-- Actual Hilbert ramification is exactly the principal-unit multiplier
predicate used by the ring-only DVR character kernel. -/
theorem mem_ramificationGroup_iff_principalUnitMultipliers
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) (σ : inertiaGroup K V) :
    σ ∈ ramificationGroup K V ↔
      ∀ x : V, ∃ a : Vˣ,
        (σ : decompositionGroup K V) • x = x * (a : V) ∧
          (a : V) - 1 ∈ IsLocalRing.maximalIdeal V := by
  change (∀ x : Lˣ,
    Units.map (((σ : decompositionGroup K V) : L ≃ₐ[K] L).toRingHom.toMonoidHom) x /
      x ∈ V.principalUnitGroup) ↔ _
  exact (DiscreteValuationRing.principalUnitMultipliers_iff_unitQuotients V
    (((σ : decompositionGroup K V) : L ≃ₐ[K] L).toRingHom)
    (MulSemiringAction.toRingHom (decompositionGroup K V) V
      (σ : decompositionGroup K V)) rfl).symm

end RamificationTheory.HilbertRamification.ValuationSubring
