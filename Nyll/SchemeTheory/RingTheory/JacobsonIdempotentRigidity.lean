/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.Ring

/-!
# Uniqueness of idempotents modulo a Jacobson ideal

An idempotent in the Jacobson radical vanishes, since its complement is a
unit annihilating it. Applying this to the two complementary products shows
that reduction modulo a Jacobson ideal is injective on idempotents.
-/

@[expose] public section

universe u

namespace IsIdempotentElem

private lemma eq_zero_of_mem_jacobson
    {R : Type u} [CommRing R] {e : R} (he : IsIdempotentElem e)
    (hmem : e ∈ Ideal.jacobson (⊥ : Ideal R)) : e = 0 := by
  have hunit : IsUnit (1 - e) := by
    apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
    have heq : (1 - e) - 1 = -e := by ring
    rw [heq]
    exact (Ideal.jacobson (⊥ : Ideal R)).neg_mem hmem
  apply hunit.mul_left_cancel
  rw [he.one_sub_mul_self, mul_zero]

/-- Two idempotents with the same image modulo an ideal in the Jacobson
radical are equal. -/
theorem eq_of_quotient_eq_of_le_jacobson
    {R : Type u} [CommRing R] (J : Ideal R) (hJ : J ≤ Ideal.jacobson ⊥)
    {e f : R} (he : IsIdempotentElem e) (hf : IsIdempotentElem f)
    (hquot : Ideal.Quotient.mk J e = Ideal.Quotient.mk J f) : e = f := by
  have hcross (a c : R) (ha : IsIdempotentElem a) (hc : IsIdempotentElem c)
      (hac : Ideal.Quotient.mk J a = Ideal.Quotient.mk J c) : a * (1 - c) = 0 := by
    apply eq_zero_of_mem_jacobson (ha.mul hc.one_sub)
    apply hJ
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_mul, map_sub, map_one, hac]
    exact (hc.map (Ideal.Quotient.mk J)).mul_one_sub_self
  have hef := hcross e f he hf hquot
  have hfe := hcross f e hf he hquot.symm
  rw [mul_sub, mul_one, sub_eq_zero] at hef hfe
  exact hef.trans ((mul_comm e f).trans hfe.symm)

end IsIdempotentElem
