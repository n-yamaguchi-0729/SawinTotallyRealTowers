/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_HenselianLocalRing_of_isIntegral_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.HenselianLocalRing_of_moduleFinite_of_isLocalRing
import Nyll.SchemeTheory.RingTheory.HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

/-!
# Henselian Local Ring of is Integral of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace HenselianLocalRing_of_isIntegral_of_isLocalRing

universe u v

namespace HensIntAux

open IsLocalRing Polynomial
open _root_.HenselianLocalRing
  (exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite)

theorem eq_zero_or_eq_one_of_isIdempotentElem {S : Type v} [CommRing S] [IsLocalRing S] (x : S)
    (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  by_cases hu : IsUnit x
  · right
    exact hu.mul_left_cancel (hx.eq.trans (mul_one x).symm)
  · left
    have h1 : IsUnit (1 - x) := (IsLocalRing.isUnit_or_isUnit_one_sub_self x).resolve_left hu
    have h2 : (1 - x) * x = (1 - x) * 0 := by rw [sub_mul, one_mul, hx.eq, sub_self, mul_zero]
    exact h1.mul_left_cancel h2

theorem isLocalRing_subalgebra {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] (S₀ : Subalgebra R S) [Module.Finite R
      S₀] :
    IsLocalRing S₀ := by
  classical
  obtain ⟨hfin, e, hce, hnot, -, -⟩ :=
    exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := R) (S := ↥S₀)
  have hidem : ∀ x : S₀, IsIdempotentElem x → x = 0 ∨ x = 1 := by
    intro x hx
    have hxS : IsIdempotentElem (x : S) := by
      change (x : S) * (x : S) = x
      rw [← Subalgebra.coe_mul, hx.eq]
    rcases eq_zero_or_eq_one_of_isIdempotentElem (x : S) hxS with h | h
    · left; exact Subtype.ext (by simpa using h)
    · right; exact Subtype.ext (by simpa using h)
  have he1 : ∀ m, e m = 1 := fun m =>
    (hidem (e m) (hce.idem m)).resolve_left (fun h0 => hnot m
      (by rw [h0]; exact (m.asIdeal).zero_mem))
  have hsub : ∀ m m' : MaximalSpectrum S₀, m = m' := by
    intro m m'
    by_contra hne
    have h : e m * e m' = 0 := hce.ortho hne
    rw [he1, he1, mul_one] at h
    exact one_ne_zero h
  obtain ⟨M, hM⟩ := Ideal.exists_maximal S₀
  exact IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' =>
    congrArg MaximalSpectrum.asIdeal (hsub ⟨M', hM'⟩ ⟨M, hM⟩)⟩

end HensIntAux

open HensIntAux IsLocalRing Polynomial in
theorem _root_.HenselianLocalRing.of_isIntegral_of_isLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [Algebra.IsIntegral R S] :
    HenselianLocalRing S := by
  classical
  refine { is_henselian := fun f hf a₀ h₁ h₂ => ?_ }
  set T : Set S := insert a₀ (↑f.coeffs : Set S) with hT
  have hTfin : T.Finite := (Finset.finite_toSet _).insert a₀
  let S₀ : Subalgebra R S := Algebra.adjoin R T
  let _ : Module.Finite R S₀ :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hTfin (fun x _ => Algebra.IsIntegral.isIntegral x)
  let _ : Algebra.IsIntegral S₀ S := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  let _ : IsLocalRing S₀ := isLocalRing_subalgebra (R := R) S₀
  let _ : HenselianLocalRing S₀ := HenselianLocalRing.of_moduleFinite_of_isLocalRing (R := R) (S :=
    ↥S₀)
  have hcomap : (maximalIdeal S).comap (algebraMap S₀ S) = maximalIdeal S₀ :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := S₀)
      (maximalIdeal S))
  have hlifts : f ∈ Polynomial.lifts (algebraMap S₀ S) := by
    refine (Polynomial.lifts_iff_coeff_lifts f).mpr fun i => ?_
    by_cases h0 : f.coeff i = 0
    · exact ⟨0, by rw [h0, map_zero]⟩
    · refine ⟨⟨f.coeff i, Algebra.subset_adjoin ?_⟩, rfl⟩
      exact Set.mem_insert_of_mem _ (Polynomial.coeff_mem_coeffs h0)
  obtain ⟨f₀, hf₀, -, hf₀m⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hf
  set b₀ : S₀ := ⟨a₀, Algebra.subset_adjoin (Set.mem_insert _ _)⟩ with hb₀
  have hev : algebraMap S₀ S (f₀.eval b₀) = f.eval a₀ := by
    rw [← hf₀, Polynomial.eval_map, ← Polynomial.eval₂_at_apply]
    rfl
  have hder : algebraMap S₀ S (f₀.derivative.eval b₀) = f.derivative.eval a₀ := by
    rw [← hf₀, Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.eval₂_at_apply]
    rfl
  have h₁' : f₀.eval b₀ ∈ maximalIdeal S₀ := by
    rw [← hcomap, Ideal.mem_comap, hev]; exact h₁
  have h₂' : IsUnit (f₀.derivative.eval b₀) := by
    by_contra hnu
    have hm : f₀.derivative.eval b₀ ∈ maximalIdeal S₀ := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← hcomap, Ideal.mem_comap, hder] at hm
    exact (IsLocalRing.mem_maximalIdeal _).mp hm h₂
  obtain ⟨a, ha, ha₀⟩ := HenselianLocalRing.is_henselian f₀ hf₀m b₀ h₁' h₂'
  refine ⟨(a : S), ?_, ?_⟩
  · change f.eval (a : S) = 0
    rw [← hf₀, Polynomial.eval_map]
    change f₀.eval₂ (algebraMap S₀ S) (algebraMap S₀ S a) = 0
    rw [Polynomial.eval₂_at_apply, ha.eq_zero, map_zero]
  · have hm := ha₀
    rw [← hcomap, Ideal.mem_comap, map_sub] at hm
    exact hm
end HenselianLocalRing_of_isIntegral_of_isLocalRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
