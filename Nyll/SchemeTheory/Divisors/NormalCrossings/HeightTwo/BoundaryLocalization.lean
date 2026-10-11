/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Associated
import Nyll.SchemeTheory.Divisors.NormalCrossings.HeightTwo.BranchSupport

/-!
# Boundary equations at height-two strict-normal-crossings points

At a height-two point containing a selected branch, at most one further
labelled branch can pass through the point.  Every other boundary parameter
becomes a unit after localization.  Consequently the localized boundary
equation is associated either to the selected parameter alone or to the
product of the selected parameter with the unique second branch.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped BigOperators

universe u

/-- At a height-two point of a split strict-normal-crossings chart, the
localized boundary equation has exactly the product of the labelled branches
through that point as its nonunit part.  Since the selected branch is fixed,
this is either one parameter or a product of two distinct parameters.

All other boundary factors are proved to be units in the localization; no
factorization or localized-boundary comparison is assumed. -/
theorem splitStrictNormalCrossings_heightTwo_localizedBoundary_associated
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A] {d r : ℕ} {f : A} {t : Fin d → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin d) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) :
    let R := Localization.AtPrime P
    Associated (algebraMap A R f) (algebraMap A R (t i)) ∨
      ∃ j : Fin d, j.1 < r ∧ j ≠ i ∧ t j ∈ P ∧
        Associated (algebraMap A R f)
          (algebraMap A R (t i) * algebraMap A R (t j)) := by
  classical
  let R := Localization.AtPrime P
  have hBoundary :
      Associated (algebraMap A R f)
        (algebraMap A R (boundaryProduct t r)) :=
    hNC.2.2.2.2.1.map (algebraMap A R)
  rcases splitStrictNormalCrossings_heightTwo_branchSupport
      hNC i P hP htiP with hone | htwo
  · left
    refine hBoundary.trans ?_
    let g : Fin d → R := fun k ↦
      if k = i then algebraMap A R (t i) else 1
    have hprod :
        Associated
          (∏ k ∈ boundaryIndices d r, algebraMap A R (t k))
          (∏ k ∈ boundaryIndices d r, g k) := by
      apply Associated.prod
      intro k hk
      have hklt : k.1 < r := by
        simpa [boundaryIndices] using hk
      by_cases hki : k = i
      · subst k
        simp [g]
      · have htkP : t k ∉ P := by
          intro hmem
          exact hki (hone k hklt hmem)
        have hunit : IsUnit (algebraMap A R (t k)) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff R P (t k)).2 htkP
        rw [show g k = 1 by simp [g, hki]]
        exact associated_one_iff_isUnit.mpr hunit
    have hg :
        (∏ k ∈ boundaryIndices d r, g k) =
          algebraMap A R (t i) := by
      simp [g, boundaryIndices, hi]
    have hmap :
        algebraMap A R (boundaryProduct t r) =
          ∏ k ∈ boundaryIndices d r, algebraMap A R (t k) := by
      simp [boundaryProduct]
    rw [hmap]
    exact hprod.trans (Associated.of_eq hg)
  · obtain ⟨j, hj, hji, htjP, hsupport⟩ := htwo
    right
    refine ⟨j, hj, hji, htjP, hBoundary.trans ?_⟩
    let g : Fin d → R := fun k ↦
      if k = i then algebraMap A R (t i)
      else if k = j then algebraMap A R (t j)
      else 1
    have hprod :
        Associated
          (∏ k ∈ boundaryIndices d r, algebraMap A R (t k))
          (∏ k ∈ boundaryIndices d r, g k) := by
      apply Associated.prod
      intro k hk
      have hklt : k.1 < r := by
        simpa [boundaryIndices] using hk
      by_cases hki : k = i
      · subst k
        simp [g]
      · by_cases hkj : k = j
        · subst k
          simp [g, hji]
        · have htkP : t k ∉ P := by
            intro hmem
            rcases hsupport k hklt hmem with h | h
            · exact hki h
            · exact hkj h
          have hunit : IsUnit (algebraMap A R (t k)) :=
            (IsLocalization.AtPrime.isUnit_to_map_iff R P (t k)).2 htkP
          rw [show g k = 1 by simp [g, hki, hkj]]
          exact associated_one_iff_isUnit.mpr hunit
    have hg :
        (∏ k ∈ boundaryIndices d r, g k) =
          algebraMap A R (t i) * algebraMap A R (t j) := by
      have hiMem : i ∈ boundaryIndices d r := by
        simp [boundaryIndices, hi]
      have hjMem : j ∈ boundaryIndices d r := by
        simp [boundaryIndices, hj]
      have hgPoint (k : Fin d) :
          g k =
            (if k = i then algebraMap A R (t i) else 1) *
              (if k = j then algebraMap A R (t j) else 1) := by
        by_cases hki : k = i
        · subst k
          simp [g, Ne.symm hji]
        · by_cases hkj : k = j
          · subst k
            simp [g, hki]
          · simp [g, hki, hkj]
      calc
        (∏ k ∈ boundaryIndices d r, g k) =
            (∏ k ∈ boundaryIndices d r,
                if k = i then algebraMap A R (t i) else 1) *
              (∏ k ∈ boundaryIndices d r,
                if k = j then algebraMap A R (t j) else 1) := by
          simp_rw [hgPoint, Finset.prod_mul_distrib]
        _ = algebraMap A R (t i) * algebraMap A R (t j) := by
          rw [Finset.prod_ite_eq_of_mem' _ i _ hiMem,
            Finset.prod_ite_eq_of_mem' _ j _ hjMem]
    have hmap :
        algebraMap A R (boundaryProduct t r) =
          ∏ k ∈ boundaryIndices d r, algebraMap A R (t k) := by
      simp [boundaryProduct]
    rw [hmap]
    exact hprod.trans (Associated.of_eq hg)

end EtaleFundamentalGroups

end
