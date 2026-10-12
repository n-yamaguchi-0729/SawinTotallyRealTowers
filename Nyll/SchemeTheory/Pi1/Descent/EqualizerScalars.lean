/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten

Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/Flat/Equalizer.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/RingTheory/Flat/Equalizer.lean
-/

/-
Nyll-maintained port: imports and proofs have been adapted for the Nyll toolchain.
Upstream notices are preserved; local changes are documented in
Nyll/EtaleFundamentalGroups/Pi1/ATTRIBUTION.md and UPSTREAM.json.
-/

module

public import Mathlib.RingTheory.TensorProduct.Maps
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Algebra.Equalizer

/-!
# Scalar restriction of algebra equalizers

Scalar restriction and tensor-product comparisons identify equalizers after
flat base change, using the original algebra homomorphisms.
-/

@[expose] public section

universe u

open TensorProduct

variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]

namespace Algebra

local notation f " ≟ₐ " g => AlgHom.equalizer f g
--local notation "eq(" f " , " g ")" => AlgHom.equalizer f g

local notation S " ⊗ₘ " f => Algebra.TensorProduct.map (AlgHom.id S S) f

variable (R) in
/-- Restricting scalars from `S` to `R` preserves the underlying equalizer subalgebra. -/
def _root_.AlgHom.equalizerRestrictScalars [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) :
    AlgHom.equalizer (f.restrictScalars R) (g.restrictScalars R) ≃ₐ[R]
      AlgHom.equalizer f g :=
  AlgEquiv.refl

@[simp]
lemma _root_.AlgHom.equalizerRestrictScalars_symm_apply [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) (x) :
    (AlgHom.equalizerRestrictScalars R f g).symm x = x :=
  rfl


end Algebra
