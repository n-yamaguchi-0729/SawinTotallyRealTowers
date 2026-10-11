/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Restriction of automorphisms to integral closures

Bundles restriction of algebra automorphisms to the integral closure as a group homomorphism.
-/

noncomputable section

namespace SchemeTheory

universe u v

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]

/-- Restrict algebra automorphisms to the actual integral closure. -/
def integralClosureAutHom :
    (B ≃ₐ[R] B) →* (integralClosure R B ≃ₐ[R] integralClosure R B) where
  toFun σ := σ.mapIntegralClosure
  map_one' := by
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.ext
    intro b
    apply Subtype.ext
    rfl

end SchemeTheory

end
