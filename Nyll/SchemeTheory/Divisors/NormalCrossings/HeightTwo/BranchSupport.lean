/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.List.Perm.Subperm
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Flat
import Nyll.SchemeTheory.Divisors.NormalCrossings.Basic

/-!
# Branch support at a height-two strict-normal-crossings point

A height-two prime contains at most two members of a regular system of
parameters.  Applied to the labelled part of a split strict-normal-crossings
chart, this gives the exact dichotomy needed by the local Abhyankar
construction: either the selected branch is the only branch through the
point, or there is one further branch and every branch through the point is
one of those two.

The proof does not use ramification data.  Three distinct parameters in the
prime would remain a three-term regular sequence after localization, whereas
the localized ring has Krull dimension two.
-/

noncomputable section

namespace EtaleFundamentalGroups

open RingTheory.Sequence
open scoped List

universe u

/-- Three members of a regular system of parameters cannot all lie in a
height-two prime.  Equivalently, once two distinct parameters in the prime
have been fixed, every further parameter in the prime is one of them. -/
theorem eq_left_or_eq_right_of_three_parameters_mem_heightTwo
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A] {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i j : Fin d) (hij : i ≠ j)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) (htjP : t j ∈ P)
    (k : Fin d) (htkP : t k ∈ P) :
    k = i ∨ k = j := by
  classical
  by_contra hk
  simp only [not_or] at hk
  have hidxNodup : [i, j, k].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, List.nodup_nil, and_true]
    exact ⟨⟨hij, fun hik ↦ hk.1 hik.symm⟩,
      ⟨fun hjk ↦ hk.2 hjk.symm, not_false⟩⟩
  have hidxSubset : [i, j, k] ⊆ List.finRange d := by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact List.mem_finRange _
  have hidxSubperm : [i, j, k] <+~ List.finRange d :=
    hidxNodup.subperm hidxSubset
  have hvalueSubperm :
      [t i, t j, t k] <+~ List.ofFn t := by
    obtain ⟨xs, hxsPerm, hxsSublist⟩ := hidxSubperm
    refine ⟨xs.map t, ?_, ?_⟩
    · simpa only [List.map_cons, List.map_nil] using hxsPerm.map t
    · simpa only [List.ofFn_eq_map] using hxsSublist.map t
  obtain ⟨ps, hpsPerm, hselectedSublist⟩ :=
    List.subperm_iff.mp hvalueSubperm
  obtain ⟨qs, hpsSelected⟩ := hselectedSublist.exists_perm_append
  have hperm : [t i, t j, t k] ++ qs ~ List.ofFn t :=
    hpsSelected.symm.trans hpsPerm
  have hregPerm : IsRegular A ([t i, t j, t k] ++ qs) :=
    IsLocalRing.isRegular_of_perm hNC.2.2.1.1 hperm.symm
  have hweakThree : IsWeaklyRegular A [t i, t j, t k] :=
    ((isWeaklyRegular_append_iff A [t i, t j, t k] qs).mp
      hregPerm.toIsWeaklyRegular).1
  let R := Localization.AtPrime P
  have hregularLocalized :
      IsRegular R
        [algebraMap A R (t i), algebraMap A R (t j),
          algebraMap A R (t k)] := by
    simpa only [R, List.map_cons, List.map_nil] using
      hweakThree.isRegular_of_isLocalization_of_mem R P (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at hx
        rcases hx with rfl | rfl | rfl
        · exact htiP
        · exact htjP
        · exact htkP)
  let I : Ideal R := Ideal.ofList
    [algebraMap A R (t i), algebraMap A R (t j), algebraMap A R (t k)]
  have hIne : I ≠ ⊤ := by
    intro hI
    apply hregularLocalized.top_ne_smul
    simp [I, hI]
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hdimension :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
      [algebraMap A R (t i), algebraMap A R (t j), algebraMap A R (t k)]
      hregularLocalized
  norm_num [List.length_cons, List.length_nil] at hdimension
  have hdimR : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim R = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P R
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hP
  have hthreeLe :
      ((3 : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim R := by
    have hnonneg : (0 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ I) :=
      ringKrullDim_nonneg_of_nontrivial
    calc
      ((3 : ℕ∞) : WithBot ℕ∞) ≤
          ringKrullDim (R ⧸ I) + ((3 : ℕ∞) : WithBot ℕ∞) := by
        calc
          ((3 : ℕ∞) : WithBot ℕ∞) =
              ((3 : ℕ∞) : WithBot ℕ∞) + 0 :=
            (add_zero _).symm
          _ ≤ ((3 : ℕ∞) : WithBot ℕ∞) +
              ringKrullDim (R ⧸ I) :=
            add_le_add_right hnonneg _
          _ = ringKrullDim (R ⧸ I) +
              ((3 : ℕ∞) : WithBot ℕ∞) := add_comm _ _
      _ = ringKrullDim R := by
        simpa [I] using hdimension
  rw [hdimR] at hthreeLe
  norm_num at hthreeLe

/-- Exact branch-support dichotomy at a height-two point containing a
selected labelled branch.  In the second case the additional branch is
distinct from the selected one and exhausts all remaining labelled branches
through the point. -/
theorem splitStrictNormalCrossings_heightTwo_branchSupport
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A] {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin d)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) :
    (∀ j : Fin d, j.1 < r → t j ∈ P → j = i) ∨
      ∃ j : Fin d, j.1 < r ∧ j ≠ i ∧ t j ∈ P ∧
        ∀ k : Fin d, k.1 < r → t k ∈ P → k = i ∨ k = j := by
  classical
  by_cases hsecond : ∃ j : Fin d, j.1 < r ∧ j ≠ i ∧ t j ∈ P
  · right
    obtain ⟨j, hj, hji, htjP⟩ := hsecond
    refine ⟨j, hj, hji, htjP, ?_⟩
    intro k _hk htkP
    exact eq_left_or_eq_right_of_three_parameters_mem_heightTwo
      hNC i j hji.symm P hP htiP htjP k htkP
  · left
    intro j hj htjP
    by_contra hji
    exact hsecond ⟨j, hj, hji, htjP⟩

end EtaleFundamentalGroups

end
