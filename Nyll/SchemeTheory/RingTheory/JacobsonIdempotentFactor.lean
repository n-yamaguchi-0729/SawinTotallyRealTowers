/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.JacobsonIntegral
public import Nyll.SchemeTheory.RingTheory.QuotientBaseChange
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Units on a lifted quotient factor

In an integral algebra over a Jacobson pair, an element congruent to the unit
of a factor becomes a unit on that factor. The factor is the actual quotient
by the complementary element, and its algebra structure comes from the base.
-/

@[expose] public section

universe u v

namespace Algebra

/-- An element congruent to `e` modulo the extended Jacobson ideal is a unit
after imposing `e = 1`. In particular, this applies to a lifted idempotent. -/
theorem isUnit_quotient_one_sub_of_eq_mod_extendedIdeal
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (b e : C)
    (hbe : Ideal.Quotient.mk (I.map (algebraMap R C)) b =
      Ideal.Quotient.mk (I.map (algebraMap R C)) e) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - e}) b) := by
  let K : Ideal C := Ideal.span {1 - e}
  let q : C →ₐ[R] C ⧸ K := Ideal.Quotient.mkₐ R K
  have : Algebra.IsIntegral R (C ⧸ K) :=
    Algebra.IsIntegral.of_surjective q Ideal.Quotient.mk_surjective
  have he : q e = 1 := by
    have h : q (1 - e) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
    rw [map_sub, map_one, sub_eq_zero] at h
    exact h.symm
  have hmem : b - e ∈ I.map (algebraMap R C) := Ideal.Quotient.eq.mp hbe
  have hmap : q (b - e) ∈ I.map (algebraMap R (C ⧸ K)) := by
    rw [← q.map_extendedIdeal I]
    exact Ideal.mem_map_of_mem q.toRingHom hmem
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  apply Ideal.map_le_jacobson_bot_of_isIntegral hI
  change q b - 1 ∈ I.map (algebraMap R (C ⧸ K))
  simpa only [map_sub, he] using hmap

end Algebra
