/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalTameCharacterGroupMap
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterKernel
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Surjectivity and kernel of the local tame character

Proves that the local tame character group map is surjective and that its kernel is the
principal-unit inertia subgroup.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (G : Type u) [Group G] [Finite G] [MulSemiringAction G R]

/-- The native map retains the actual finite character's surjectivity. -/
theorem localTameCharacterGroupMap_surjective :
    Function.Surjective (localTameCharacterGroupMap R G).toFun :=
  tameCharacter_surjective R G

/-- Its kernel is the same original principal-unit subgroup. -/
theorem localTameCharacterGroupMap_ker :
    (localTameCharacterGroupMap R G).ker = principalUnitInertia R G :=
  tameCharacter_ker R G

end RamificationTheory.HilbertRamification.DiscreteValuationRing
