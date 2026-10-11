/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Group objects for the local tame character

Defines group objects for local inertia and the roots of unity of the tame order. It presents
the finite local tame character as a homomorphism between them.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

/-- The native group of actual local inertia. -/
def localInertiaGroupObject (R : Type u) [CommRing R] [IsLocalRing R]
    (G : Type v) [Group G] [MulSemiringAction G R] : GrpCat.{v} :=
  GrpCat.of ((maximalIdeal R).inertia G)

/-- The actual full root group of the computed finite tame order. -/
def localTameRootsGroupObject (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (G : Type v) [Group G] [MulSemiringAction G R] : GrpCat.{u} :=
  GrpCat.of (rootsOfUnity (tameOrder R G) (ResidueField R))

/-- The actual finite local character, retained as its ordinary monoid homomorphism. -/
def localTameCharacterGroupMap (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (G : Type u) [Group G] [Finite G] [MulSemiringAction G R] :
    localInertiaGroupObject R G →* localTameRootsGroupObject R G :=
  tameCharacter R G

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
