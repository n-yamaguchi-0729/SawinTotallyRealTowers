/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.Ideal
import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations

/-!
# Cyclic tame inertia for exponential valuations

This file is the field-valued entry point for the DVR cyclicity theorem.
A discrete production `ExponentialValuation` supplies a discrete valuation
ring, so cyclicity follows directly from the valuation-subring theorem in
`CyclicInertia.Ideal`.
-/

noncomputable section

universe u v

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

/-- The inertia group attached to a discrete exponential valuation is
cyclic when its order is prime to the exponential residue characteristic. -/
theorem discreteExponentialValuation_inertiaGroup_isCyclic_of_card_coprime_ringExpChar
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hw : LubinTate.Valuations.DiscreteExponentialValuation w)
    [Finite (inertiaGroup K
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w))]
    (hcop : Nat.Coprime
      (Nat.card (inertiaGroup K
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w)))
      (ringExpChar (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w)))) :
    IsCyclic (inertiaGroup K
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w)) := by
  let V :=
    LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w
  let : IsDiscreteValuationRing V := by
    change IsDiscreteValuationRing
      (LubinTate.Valuations.exponentialValuationSubring w)
    exact
      LubinTate.Valuations.discreteExponentialValuationSubring_isDiscreteValuationRing
        hw
  exact inertiaGroup_isCyclic_of_card_coprime_ringExpChar_of_dvr K V hcop

/-- The maximal-ideal inertia group attached to a discrete exponential
valuation is cyclic under the same coprimality condition. -/
theorem discreteExponentialValuation_maximalIdealInertia_isCyclic_of_card_coprime_ringExpChar
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hw : LubinTate.Valuations.DiscreteExponentialValuation w)
    [Finite (inertiaGroup K
      (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w))]
    (hcop : Nat.Coprime
      (Nat.card
        ((IsLocalRing.maximalIdeal
          (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
            w)).toAddSubgroup.inertia
            (decompositionGroup K
              (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w))))
      (ringExpChar (IsLocalRing.ResidueField
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w)))) :
    IsCyclic
      ((IsLocalRing.maximalIdeal
        (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring
            w)).toAddSubgroup.inertia
          (decompositionGroup K
            (LubinTate.Valuations.exponentialValuationSubringAsValuationSubring w))) := by
  rw [TameInertiaCyclicCore.valuationSubring_maximalIdeal_inertia_eq] at hcop ⊢
  exact
    discreteExponentialValuation_inertiaGroup_isCyclic_of_card_coprime_ringExpChar
      K w hw hcop

end TameAbhyankar.SGA1

end
