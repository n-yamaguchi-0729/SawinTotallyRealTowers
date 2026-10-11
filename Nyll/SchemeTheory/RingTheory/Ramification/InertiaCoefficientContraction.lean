/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Contraction of inertia difference conditions

Proves that the inertia difference condition descends to a contracted ideal along a commuting
square of coefficient maps.
-/

namespace SchemeTheory

universe u v

/-- The actual inertia difference condition descends along a proved
coefficient square to the literal contracted prime. -/
theorem inertiaDifference_comap_of_coefficient_square
    {B : Type u} {C : Type v} [CommRing B] [CommRing C]
    (f : B →+* C) (s : B →+* B) (t : C →+* C) (Q : Ideal C)
    (hcomm : f.comp s = t.comp f)
    (ht : ∀ c : C, t c - c ∈ Q) :
    ∀ b : B, s b - b ∈ Q.comap f := by
  intro b
  change f (s b - b) ∈ Q
  rw [map_sub]
  have h := congrArg (fun g : B →+* C => g b) hcomm
  change f (s b) = t (f b) at h
  rw [h]
  exact ht (f b)

end SchemeTheory
