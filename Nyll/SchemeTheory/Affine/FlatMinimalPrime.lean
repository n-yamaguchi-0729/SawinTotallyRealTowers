/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.Affine.GeometricIrreducibility

/-!
# Minimal primes under flat affine maps

Going down sends a minimal prime of a flat algebra to a minimal prime of the
base.  Over a domain the base has only the zero minimal prime, so every
irreducible component of the affine source dominates the base.
-/


namespace Ideal

universe u v

/-- The contraction of a minimal prime along a flat algebra over a domain is
the zero ideal. -/
theorem under_eq_bot_of_mem_minimalPrimes_of_flat
    {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain R] [Module.Flat R S]
    (Q : Ideal S) (hQ : Q ∈ minimalPrimes S) :
    Q.under R = ⊥ := by
  simpa only [IsDomain.minimalPrimes_eq_singleton_bot,
    Set.mem_singleton_iff] using
    Q.under_mem_minimalPrimes R hQ

end Ideal
