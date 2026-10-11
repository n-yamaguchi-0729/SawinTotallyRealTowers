/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.DeterminantTrickCongruence
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Tactic.Ring

/-!
# Annihilators of idempotents modulo an ideal

An element of a finite algebra that becomes idempotent modulo an extended
ideal admits a monic annihilator reducing to `(X - 1) ^ n * X ^ n`, with
positive `n`. Splitting a finite generating family into its multiples by
`b` and `1 - b` gives a diagonal multiplication action modulo the ideal.
No freeness, Jacobson condition, or cyclicity hypothesis is needed.
-/

@[expose] public section

open Polynomial

universe u v

namespace Algebra

/-- An element that is idempotent modulo an extended ideal has a monic
annihilator whose reduction is a product of equal positive powers of
`X - 1` and `X`. -/
theorem exists_monic_annihilator_of_quotient_idempotent
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] (I : Ideal R) (b : B)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R B)) b)) :
    ∃ n ≥ 1, ∃ p : R[X], p.Monic ∧ aeval b p = 0 ∧
      p.map (Ideal.Quotient.mk I) = (X - 1) ^ n * X ^ n := by
  classical
  let J : Ideal B := I.map (algebraMap R B)
  have hbdef : b * b - b ∈ J := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, sub_eq_zero]
    exact hb.eq
  obtain ⟨n, u, hu⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Module.Finite.fg_top : (⊤ : Submodule R B).FG)
  let v : Fin n ⊕ Fin n → B := fun j ↦ match j with
    | .inl i => b * u i
    | .inr i => (1 - b) * u i
  let d : Fin n ⊕ Fin n → R := fun j ↦ match j with
    | .inl _ => 1
    | .inr _ => 0
  let N : Submodule R B := Submodule.span R (Set.range v)
  have hv : N = ⊤ := by
    apply top_unique
    refine hu.ge.trans (Submodule.span_le.mpr ?_)
    rintro x ⟨i, rfl⟩
    have hleft : b * u i ∈ N := Submodule.subset_span ⟨Sum.inl i, rfl⟩
    have hright : (1 - b) * u i ∈ N := Submodule.subset_span ⟨Sum.inr i, rfl⟩
    have heq : b * u i + (1 - b) * u i = u i := by ring
    exact heq ▸ N.add_mem hleft hright
  have hres (j : Fin n ⊕ Fin n) :
      Algebra.lmul R B b (v j) - d j • v j ∈ I • (⊤ : Submodule R B) := by
    rw [Ideal.smul_top_eq_map]
    cases j with
    | inl i =>
      change b * (b * u i) - (1 : R) • (b * u i) ∈ J
      rw [one_smul]
      have heq : b * (b * u i) - b * u i = (b * b - b) * u i := by ring
      rw [heq]
      exact J.mul_mem_right (u i) hbdef
    | inr i =>
      change b * ((1 - b) * u i) - (0 : R) • ((1 - b) * u i) ∈ J
      rw [zero_smul, sub_zero]
      have heq : b * ((1 - b) * u i) = -(b * b - b) * u i := by ring
      rw [heq]
      exact J.mul_mem_right (u i) (J.neg_mem hbdef)
  obtain ⟨p, hpmonic, hpEnd, hpmap⟩ :=
    LinearMap.exists_monic_aeval_eq_zero_map_eq_prod_of_residual_diagonal
      I (Algebra.lmul R B b) v hv d hres
  have hproot : aeval b p = 0 := by
    apply Algebra.lmul_injective (R := R) (A := B)
    rw [← Polynomial.aeval_algHom_apply (Algebra.lmul R B) b p, map_zero]
    exact hpEnd
  have hpmap' : p.map (Ideal.Quotient.mk I) = (X - 1) ^ n * X ^ n := by
    simpa only [Fintype.prod_sum_type, d, map_one, map_zero, Polynomial.C_1,
      Polynomial.C_0, sub_zero, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] using hpmap
  have hmonic : (X - (1 : R[X])).Monic := by
    simpa only [Polynomial.C_1] using monic_X_sub_C (1 : R)
  refine ⟨n + 1, Nat.succ_le_succ (Nat.zero_le n), p * (X - 1) * X,
    (hpmonic.mul hmonic).mul monic_X, ?_, ?_⟩
  · simp only [aeval_mul, hproot, zero_mul]
  · simp only [Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_one, hpmap', pow_succ]
    ring

end Algebra
