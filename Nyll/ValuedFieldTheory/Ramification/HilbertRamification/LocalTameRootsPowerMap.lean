/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalTameCharacterGroupMap
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.FiniteResidueCharacterScaling
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Power maps on local tame root groups

Defines power homomorphisms on the local tame root group and proves injectivity for exponential-
characteristic powers. These maps are surjective when the acting group is finite.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (G : Type v) [Group G] [MulSemiringAction G R]

/-- The canonical power map on the actual finite root group. -/
def localTameRootsPowerGroupMap (m : ℕ) :
    localTameRootsGroupObject R G →* localTameRootsGroupObject R G :=
  (powMonoidHom m : rootsOfUnity (tameOrder R G) (ResidueField R) →* _)

/-- Exponential-characteristic powers are injective on the actual roots,
by the native residue-field Frobenius argument. -/
theorem localTameRootsPowerGroupMap_injective
    (p a : ℕ) [ExpChar (ResidueField R) p] :
    Function.Injective (localTameRootsPowerGroupMap R G (p ^ a)) := by
  intro x y h
  change x ^ (p ^ a) = y ^ (p ^ a) at h
  apply Subtype.ext
  apply residueUnits_expCharPow_injective p a
  exact congrArg (fun z : rootsOfUnity (tameOrder R G) (ResidueField R) => z.val) h

/-- Exponential-characteristic power maps are bijective on these actual
finite root groups, with no perfectness premise. -/
theorem localTameRootsPowerGroupMap_surjective [Finite G]
    (p a : ℕ) [ExpChar (ResidueField R) p] :
    Function.Surjective (localTameRootsPowerGroupMap R G (p ^ a)) := by
  have : NeZero (tameOrder R G) := ⟨Nat.ne_of_gt (tameOrder_pos R G)⟩
  exact finiteSubgroup_expCharPow_surjective
    (rootsOfUnity (tameOrder R G) (ResidueField R)) p a

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
