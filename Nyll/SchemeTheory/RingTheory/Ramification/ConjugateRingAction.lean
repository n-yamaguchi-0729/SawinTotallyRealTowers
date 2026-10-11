/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Equiv

/-!
# Conjugation of ring automorphisms

Proves the commuting square for conjugating a ring automorphism through a ring equivalence. It
also transports a compatible ambient coefficient square to the conjugated automorphism.
-/

namespace SchemeTheory

universe u v w

/-- Conjugating an actual automorphism through a ring equivalence gives the
actual commuting action square. -/
theorem ringEquiv_conjugate_commutes
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (σ : R ≃+* R) :
    e.toRingHom.comp σ.toRingHom =
      (e.symm.trans (σ.trans e)).toRingHom.comp e.toRingHom := by
  apply RingHom.ext
  intro x
  change e (σ x) = e (σ (e.symm (e x)))
  rw [e.symm_apply_apply]

/-- The original field coefficient square passes to the actual conjugated
ring automorphism. -/
theorem ringEquiv_conjugate_field_square
    {R : Type u} {S : Type v} {F : Type w}
    [CommRing R] [CommRing S] [CommRing F]
    (e : R ≃+* S) (σ : R ≃+* R) (i : S →+* F) (ρ : F →+* F)
    (hfield : (i.comp e.toRingHom).comp σ.toRingHom =
      ρ.comp (i.comp e.toRingHom)) :
    i.comp (e.symm.trans (σ.trans e)).toRingHom = ρ.comp i := by
  apply RingHom.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  change i (e (σ (e.symm (e x)))) = ρ (i (e x))
  rw [e.symm_apply_apply]
  exact RingHom.congr_fun hfield x

end SchemeTheory
