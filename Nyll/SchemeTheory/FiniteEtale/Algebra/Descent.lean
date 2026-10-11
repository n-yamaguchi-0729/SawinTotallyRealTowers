/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Descent.lean
-/

module

public import Mathlib.RingTheory.Etale.Descent
public import Nyll.SchemeTheory.FiniteEtale.Algebra.Basic

/-!
# Faithfully flat descent of finite etale algebras

An algebra whose tensor product with a faithfully flat base algebra is finite etale is
itself finite etale, by descending etaleness and module finiteness separately.
-/

@[expose] public section

universe u v w

open TensorProduct

lemma Algebra.FiniteEtale.of_finiteEtale_tensorProduct_of_faithfullyFlat {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S]
    (T : Type u) [CommRing T] [Algebra R T] [Module.FaithfullyFlat R T]
    [Algebra.FiniteEtale T (T ⊗[R] S)] :
    Algebra.FiniteEtale R S := by
  have : Algebra.Etale R S :=
    .of_etale_tensorProduct_of_faithfullyFlat T
  have : Module.Finite R S :=
    .of_finite_tensorProduct_of_faithfullyFlat T
  constructor
