/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Aut

/-!
# Reflection of automorphism powers along injections

Proves that a power of a ring automorphism is the identity whenever the same power of a
compatible extension is the identity and the coefficient map is injective.
-/

namespace SchemeTheory

universe u v

/-- The order of an actual coefficient automorphism is reflected by its
injective field extension; the iterated coefficient square is proved. -/
theorem ringEquiv_pow_eq_one_of_extension
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f)
    (σ : R ≃+* R) (ρ : S ≃+* S)
    (hcoeff : ρ.toRingHom.comp f = f.comp σ.toRingHom)
    (n : ℕ) (hρ : ρ ^ n = 1) : σ ^ n = 1 := by
  have hc (x : R) : ρ (f x) = f (σ x) := RingHom.congr_fun hcoeff x
  have hp : ∀ (m : ℕ) (x : R), (ρ ^ m) (f x) = f ((σ ^ m) x) := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m hm =>
      intro x
      simp only [pow_succ, RingAut.mul_apply]
      rw [hc, hm]
  apply RingEquiv.ext
  intro x
  apply hf
  have h := hp n x
  rw [hρ] at h
  exact h.symm

end SchemeTheory
