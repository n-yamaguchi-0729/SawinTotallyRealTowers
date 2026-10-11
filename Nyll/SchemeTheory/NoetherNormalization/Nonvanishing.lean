/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Nonvanishing evaluations over infinite fields

This file supplies the nonvanishing step used in the constructive proof of
Fried--Jarden, Lemma 22.5.1, and hence in the linear refinement of
Proposition 6.2.1.  The second theorem says that dehomogenizing a nonzero
homogeneous polynomial by setting one coordinate equal to `1` remains
nonzero.
-/

namespace FieldArithmetic
namespace Chapter06

open Cardinal Polynomial
open MvPolynomial

variable {K : Type*} [Field K] [Infinite K]

/--
A nonzero multivariable polynomial in finitely many variables over an infinite
field has a nonzero evaluation.
-/
theorem exists_eval_ne_zero_fin :
    ∀ {n : ℕ} {F : MvPolynomial (Fin n) K}, F ≠ 0 → ∃ r, eval r F ≠ 0
  | 0, F, hF => by
      use 0
      contrapose hF
      ext d
      simpa only [Subsingleton.elim d 0, MvPolynomial.eval_zero,
        AddMonoidAlgebra.coeff_zero] using! hF
  | n + 1, F, hF => by
      let p : Polynomial (MvPolynomial (Fin n) K) := finSuccEquiv K n F
      have hp : p ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hF
      obtain ⟨i, hi⟩ : ∃ i : ℕ, p.coeff i ≠ 0 := by
        contrapose! hp
        exact Polynomial.ext hp
      obtain ⟨r, hr⟩ := exists_eval_ne_zero_fin hi
      let q : K[X] := p.map (eval r)
      have hq : q ≠ 0 := by
        intro hq
        apply hr
        rw [← MvPolynomial.coeff_eval_eq_eval_coeff (Fin n) r p i]
        change q.coeff i = 0
        rw [hq, Polynomial.coeff_zero]
      have hqK : q.natDegree < #K :=
        lt_of_lt_of_le Cardinal.natCast_lt_aleph0
          (Cardinal.infinite_iff.mp ‹Infinite K›)
      obtain ⟨y, hy⟩ := q.exists_eval_ne_zero_of_natDegree_lt_card hq hqK
      use Fin.cons y r
      rwa [eval_eq_eval_mv_eval']

/--
If `F` is a nonzero homogeneous polynomial, then its first coordinate can be
fixed to `1` while retaining a nonzero evaluation.

This is the dehomogenization argument behind the choice of the coefficients
`cᵢ` in Fried--Jarden, Lemma 22.5.1.
-/
theorem exists_eval_finCons_one_ne_zero
    {n d : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0) :
    ∃ r : Fin n → K, eval (Fin.cons 1 r) F ≠ 0 := by
  let p : Polynomial (MvPolynomial (Fin n) K) := finSuccEquiv K n F
  let q : MvPolynomial (Fin n) K := Polynomial.eval 1 p
  have hq : q ≠ 0 := by
    obtain ⟨s, hs⟩ : ∃ s, F.coeff s ≠ 0 := by
      contrapose! hF₀
      ext s
      simpa using hF₀ s
    have hs_degree : s 0 + s.tail.degree = d := by
      have hs_degree' := hF hs
      rw [← Finsupp.cons_tail s] at hs_degree'
      simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one,
        Finsupp.sum_cons] at hs_degree'
      have htail_degree :
          s.tail.sum (fun _ e => e) = s.tail.degree := by
        rfl
      rw [htail_degree] at hs_degree'
      exact hs_degree'
    have hi : s 0 ∈ p.support := by
      rw [Polynomial.mem_support_iff]
      intro hi
      apply hs
      rw [← Finsupp.cons_tail s, ← finSuccEquiv_coeff_coeff]
      change (p.coeff (s 0)).coeff s.tail = 0
      simp only [hi, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    intro hq₀
    apply hs
    have hcoeff := congrArg (fun g : MvPolynomial (Fin n) K ↦ g.coeff s.tail) hq₀
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
    rw [show q.coeff s.tail = F.coeff s by
      dsimp only [q]
      rw [Polynomial.eval_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
      simp only [one_pow, mul_one]
      rw [Finset.sum_eq_single (s 0)]
      · simpa only [p, Finsupp.cons_tail] using
          finSuccEquiv_coeff_coeff s.tail F (s 0)
      · intro j hj hji
        change (p.coeff j).coeff s.tail = 0
        rw [show p = finSuccEquiv K n F from rfl, finSuccEquiv_coeff_coeff]
        apply hF.coeff_eq_zero
        rw [Finsupp.degree_eq_weight_one]
        simp only [Finsupp.weight_apply, smul_eq_mul, mul_one, Finsupp.sum_cons]
        have htail_degree :
            s.tail.sum (fun _ e => e) = s.tail.degree := by
          rfl
        rw [htail_degree]
        omega
      · exact fun h => (h hi).elim] at hcoeff
    exact hcoeff
  obtain ⟨r, hr⟩ := exists_eval_ne_zero_fin hq
  use r
  intro hzero
  apply hr
  calc
    eval r q = Polynomial.eval 1 (Polynomial.map (eval r) p) := by
      simpa only [q, map_one] using
        (Polynomial.eval_map_apply (f := eval r) (p := p) 1).symm
    _ = eval (Fin.cons 1 r) F := (eval_eq_eval_mv_eval' r 1 F).symm
    _ = 0 := hzero

/--
The last-coordinate version of `exists_eval_finCons_one_ne_zero`, in the form
used in Fried--Jarden's triangular change of variables.
-/
theorem exists_eval_finSnoc_one_ne_zero
    {n d : ℕ} {F : MvPolynomial (Fin (n + 1)) K}
    (hF : F.IsHomogeneous d) (hF₀ : F ≠ 0) :
    ∃ r : Fin n → K, eval (Fin.snoc r 1) F ≠ 0 := by
  let e : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)
  let G : MvPolynomial (Fin (n + 1)) K := rename e F
  have hG : G.IsHomogeneous d := by
    exact hF.rename_isHomogeneous
  have hG₀ : G ≠ 0 := by
    intro hzero
    apply hF₀
    apply rename_injective e e.injective
    simpa only [G, map_zero] using hzero
  obtain ⟨r, hr⟩ := exists_eval_finCons_one_ne_zero hG hG₀
  use r
  simpa only [G, e, eval_rename, Function.comp_def, Fin.snoc_eq_cons_rotate] using hr

end Chapter06
end FieldArithmetic
