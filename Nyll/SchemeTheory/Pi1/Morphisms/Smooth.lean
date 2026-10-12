/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-
Adapted from the pinned pi1 source:
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/RingTheory/RingHom/Smooth.lean
-/

/-
This is a Nyll-maintained port, not an unmodified upstream file.
Local changes adapt imports, proofs and API compatibility to the pinned Nyll toolchain.
Upstream notices above apply to the upstream-derived code; they are not replaced by
Nyll authorship. Revision, file hashes and modification provenance are recorded in
Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json and ATTRIBUTION.md.
-/

module

public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.TotallySplit

/-!
# Localization criteria for smooth ring maps

Smoothness satisfies the localization-span criterion. Bijective algebra maps give formally
smooth algebras, and fraction fields of multivariate polynomial algebras are formally smooth.
-/

@[expose] public section

open TensorProduct

universe u

lemma Algebra.FormallySmooth.of_bijective_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    Algebra.FormallySmooth R S :=
  Algebra.FormallySmooth.of_equiv
    { __ := RingEquiv.ofBijective (algebraMap R S) h, commutes' := by simp }

namespace Algebra

instance {k ι : Type u} [Field k] : FormallySmooth k (FractionRing (MvPolynomial ι k)) :=
  have : FormallySmooth k (MvPolynomial ι k) := inferInstance
  have : FormallySmooth (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) :=
    .of_isLocalization (nonZeroDivisors _)
  .comp k (MvPolynomial ι k) (FractionRing (MvPolynomial ι k))

end Algebra
