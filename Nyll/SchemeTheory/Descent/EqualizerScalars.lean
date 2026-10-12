/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

module

public import Nyll.SchemeTheory.Pi1.Descent.EqualizerScalars

/-!
# The forward scalar-restriction computation

This Nyll lemma computes the forward map of pi1's equalizer scalar comparison.
The comparison itself and its upstream notices remain in the imported Pi1 module.
-/

@[expose] public section

universe u
variable {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R S] [Algebra R B]
namespace Algebra

@[simp]
lemma _root_.AlgHom.equalizerRestrictScalars_apply [Algebra S A] [Algebra S B]
    [IsScalarTower R S A] [IsScalarTower R S B]
    (f g : A →ₐ[S] B) (x) :
    AlgHom.equalizerRestrictScalars R f g x = x :=
  rfl


end Algebra
