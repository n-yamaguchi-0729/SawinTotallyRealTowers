/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingFiniteTameCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacterConjugation
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Uniformizer and conjugation formulas for tame characters

Computes powers of the tame character using any uniformizer and proves their compatibility with
conjugation and the residue-field action.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v

attribute [local instance] maximalIdeal_inertia_normal

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (G : Type v) [Group G] [Finite G] [MulSemiringAction G R]

/-- Every power of the actual tame character is computed using any
uniformizer. In particular this applies to the original e/n exponent. -/
theorem tameCharacter_pow_eq_uniformizer
    (m : ℕ) (π : R) (hπ : Irreducible π)
    (σ : (maximalIdeal R).inertia G) :
    (((tameCharacter R G).toFun σ) ^ m).val.val =
      (residue R (uniformizerRatioUnit R G π hπ σ.val).val) ^ m := by
  change (((inertiaResidueCharacter R G).toFun σ).val) ^ m =
    (residue R (uniformizerRatioUnit R G π hπ σ.val).val) ^ m
  exact congrArg (fun z : ResidueField R => z ^ m)
    (congrArg
      (fun f : (maximalIdeal R).inertia G →* (ResidueField R)ˣ => (f.toFun σ).val)
      (inertiaResidueCharacter_eq_uniformizer R G π hπ))

/-- The actual finite root character, with the same normalization power
on both sides, intertwines group conjugation and the standard residue action. -/
theorem tameCharacter_pow_conj
    (m : ℕ) (g : G) (σ : (maximalIdeal R).inertia G) :
    ((tameCharacter R G).toFun
        (((MulAut.conjNormal (H := (maximalIdeal R).inertia G)).toFun g).toFun σ)) ^ m =
      (restrictRootsOfUnity (MulSemiringAction.toRingHom G (ResidueField R) g)
        (tameOrder R G)).toFun (((tameCharacter R G).toFun σ) ^ m) := by
  apply rootsOfUnity.coe_injective
  change (((inertiaResidueCharacter R G).toFun
      (((MulAut.conjNormal (H := (maximalIdeal R).inertia G)).toFun g).toFun σ)).val) ^ m =
    (MulSemiringAction.toRingHom G (ResidueField R) g)
      ((((inertiaResidueCharacter R G).toFun σ).val) ^ m)
  rw [map_pow]
  exact congrArg (fun z : ResidueField R => z ^ m)
    (congrArg (fun a : (ResidueField R)ˣ => a.val)
      (inertiaResidueCharacter_conj R G g σ))

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
