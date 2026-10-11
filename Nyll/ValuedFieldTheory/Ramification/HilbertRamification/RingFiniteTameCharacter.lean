/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterKernel
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteSubgroupRootsOfUnity

/-!
# Finite tame characters of discrete valuation rings

Defines the tame order as the size of the inertia-character image and constructs a surjective
character onto all roots of unity of that order. It identifies the principal-unit kernel and
produces a primitive root in the residue field.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (G : Type v) [Group G] [MulSemiringAction G R]

/-- The order of the image of the actual, constructed DVR inertia character. -/
def tameOrder : ℕ := Nat.card (inertiaResidueCharacter R G).range

variable [Finite G]

theorem tameOrder_pos : 0 < tameOrder R G := by
  let f := inertiaResidueCharacter R G
  have : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact Nat.card_pos

/-- The actual finite DVR inertia character with its full root-group target. -/
def tameCharacter : (maximalIdeal R).inertia G →*
    rootsOfUnity (tameOrder R G) (ResidueField R) :=
  finiteImageRootsCharacter (inertiaResidueCharacter R G)

theorem tameCharacter_surjective : Function.Surjective (tameCharacter R G) :=
  finiteImageRootsCharacter_surjective (inertiaResidueCharacter R G)

/-- The full root-codomain character has the actual principal-unit kernel. -/
theorem tameCharacter_ker :
    (tameCharacter R G).ker = principalUnitInertia R G := by
  rw [principalUnitInertia_eq_character_ker]
  exact finiteImageRootsCharacter_ker (inertiaResidueCharacter R G)

/-- All finite tame orders occur as actual primitive roots in the residue field. -/
theorem exists_primitiveRoot_tameOrder :
    ∃ ζ : ResidueField R, IsPrimitiveRoot ζ (tameOrder R G) := by
  let f := inertiaResidueCharacter R G
  have : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  exact exists_primitiveRoot_card_finiteSubgroup f.range

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
