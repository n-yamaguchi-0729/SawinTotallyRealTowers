/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Finite.lean
-/

module

public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Finiteness of the algebra map

The ring-homomorphism finiteness property of an algebra map is equivalent to finiteness
of the target as a module over the source ring.
-/

@[expose] public section

universe u

lemma RingHom.finite_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] : (algebraMap R S).Finite ↔ Module.Finite R S := by
  simp only [RingHom.Finite]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl
