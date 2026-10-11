/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean
Original mathlib source:
https://github.com/leanprover-community/mathlib4/blob/53f8a93a7739dd4eb33926f645811ebb6cee21bf/Mathlib/AlgebraicGeometry/Morphisms/Flat.lean
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-!
# Openness and immersion consequences of flatness

Flat ring maps of finite presentation induce open maps on prime spectra. Flat scheme
morphisms with the stated finiteness, surjectivity, or monomorphism hypotheses give
isomorphisms and open immersions.
-/

@[expose] public section

universe u v

open TensorProduct

open CategoryTheory Limits MorphismProperty

lemma RingHom.Flat.isOpenMap_comap_of_finitePresentation
    {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : f.Flat)
    (hfin : f.FinitePresentation) :
    IsOpenMap (PrimeSpectrum.comap f) := by
  algebraize [f]
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

namespace AlgebraicGeometry

instance (priority := low) Flat.isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [QuasiCompact f] [Surjective f] [Mono f] : IsIso f :=
  isIso_of_surjective_of_mono f

instance (priority := low) Flat.isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    [LocallyOfFinitePresentation f] [Mono f] : IsOpenImmersion f :=
  IsOpenImmersion.of_flat_of_mono f

end AlgebraicGeometry
