/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalTameCharacterGroupMap
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingTameCharacterProperties
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

/-!
# Conjugation values of the local tame character

Computes powers of the local tame character on conjugate inertia elements using the root-group
map induced by the residue-field action.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u

attribute [local instance] maximalIdeal_inertia_normal

/-- The proved same-character equation on the literal conjugate, using the
existing native map of roots induced by the standard residue coefficient map. -/
theorem localTameCharacterGroupMap_pow_conj_value
    (R G : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Group G] [Finite G] [MulSemiringAction G R]
    (m : ℕ) (g : G) (σ : (maximalIdeal R).inertia G) :
    ((localTameCharacterGroupMap R G).toFun
      ⟨g * σ.val * g⁻¹, (maximalIdeal_inertia_normal R G).conj_mem σ.val σ.property g⟩) ^ m =
      (rootsGroupMap (MulSemiringAction.toRingHom G (ResidueField R) g)
        (tameOrder R G)).hom'.toFun (((localTameCharacterGroupMap R G).toFun σ) ^ m) :=
  tameCharacter_pow_conj R G m g σ

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
