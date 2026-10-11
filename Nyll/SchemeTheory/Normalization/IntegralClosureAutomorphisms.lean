/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Invariant.Galois
import Mathlib.RingTheory.IsGaloisGroup.Defs
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Automorphisms of finite Galois integral closures

Proves that the algebra automorphism group of the integral closure in a finite Galois extension
forms a Galois group over the integrally closed base domain.
-/

namespace SchemeTheory

universe u v w

/-- The intrinsic automorphisms of an actual finite Galois normalization
are its Galois group. The invariant-ring assertion is the native theorem
proved through actual fraction-field restriction. -/
theorem integralClosure_automorphisms_isGaloisGroup
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisGroup (integralClosure A L ≃ₐ[A] integralClosure A L) A (integralClosure A L) := by
  have : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
  exact
    { faithful := inferInstance
      commutes := inferInstance
      isInvariant := Algebra.isInvariant_of_isGalois' A K L (integralClosure A L) }

end SchemeTheory
