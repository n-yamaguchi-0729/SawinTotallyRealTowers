/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter

/-!
# Ring coefficients of uniformizer-ratio units

Extracts a ring coefficient from the uniformizer-ratio unit, together with its unit property and
the equation relating a uniformizer to its image under the action.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

/-- The actual ratio unit supplies an ordinary local coefficient, its unit
proof, and its literal value. Unit coercions remain in this sparse local owner. -/
theorem uniformizerRatioUnit_exists_coefficient
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : Type v) [Group G] [MulSemiringAction G R]
    (π : R) (hπ : Irreducible π) (g : G) :
    ∃ c : R, IsUnit c ∧
      π * c = (MulSemiringAction.toRingHom G R g).toFun π ∧
      c = (uniformizerRatioUnit R G π hπ g).val := by
  refine ⟨(uniformizerRatioUnit R G π hπ g).val, ?_, ?_, rfl⟩
  · exact (uniformizerRatioUnit R G π hπ g).isUnit
  · exact uniformizerRatioUnit_spec R G π hπ g

end RamificationTheory.HilbertRamification.DiscreteValuationRing
