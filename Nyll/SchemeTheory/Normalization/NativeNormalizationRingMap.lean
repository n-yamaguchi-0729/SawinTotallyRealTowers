/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Ring.Subsemiring.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Ring maps induced on normalizations

Restricts an algebra homomorphism to a ring homomorphism between integral closures, using
preservation of integral elements.
-/

noncomputable section

namespace SchemeTheory

universe u v

/-- The actual map on integral closures, retaining only its native ring map.
The restriction is defined by the existing preservation of integral elements. -/
def nativeNormalizationRingMap {A : Type u} [CommRing A]
    (R : CommAlgCat.{v} A) (S : CommAlgCat.{v} A) (f : R →ₐ[A] S) :
    normalizationCommAlgCat A R →+* normalizationCommAlgCat A S :=
  f.toRingHom.restrict (integralClosure A R) (integralClosure A S)
    (fun _ hx => hx.map f)

end SchemeTheory

end
