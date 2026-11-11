/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.ValuedFieldTheory.Ramification.Herbrand.Function

/-!
# Depth sums for the actual lower filtration

The exact threshold `n + 1 ≤ depth sigma` determines the interpolation formula and the
normalized Herbrand sum for every real parameter at least `-1`. The denominator is the
cardinality of the actual zeroth subgroup. Infinite depth is truncated to the same real bound.

The historical truncation names are retained here so field and finite-group consumers use
one value and one proof owner, without an import from the field-facing Herbrand theorem.
-/

@[expose] public section

noncomputable section

namespace RamificationTheory.HilbertRamification
namespace Higher

open RamificationTheory.DiscreteValuationField

/-- `min {i,r}`, with the extended value `infinity` truncated to `r`. -/
def truncateENatAtDVF (i : ℕ∞) (r : ℝ) : ℝ :=
  ENat.recTopCoe r (fun n => min (n : ℝ) r) i

/-- States the theorem `truncateENatAtDVF_top`. -/
@[simp] theorem truncateENatAtDVF_top (r : ℝ) :
    truncateENatAtDVF ⊤ r = r := by
  rfl

/-- States the theorem `truncateENatAtDVF_coe`. -/
@[simp] theorem truncateENatAtDVF_coe (n : ℕ) (r : ℝ) :
    truncateENatAtDVF (n : ℕ∞) r = min (n : ℝ) r := by
  rfl

/-- States the theorem `truncateENatAtDVF_eq_right_of_natCast_le`. -/
theorem truncateENatAtDVF_eq_right_of_natCast_le
    {i : ℕ∞} {m : ℕ} {r : ℝ} (hr : r ≤ m) (hi : (m : ℕ∞) ≤ i) :
    truncateENatAtDVF i r = r := by
  induction i using ENat.recTopCoe with
  | top => exact truncateENatAtDVF_top r
  | coe n =>
      simp only [truncateENatAtDVF_coe]
      rw [min_eq_right]
      have hmn : m ≤ n := by exact_mod_cast hi
      exact hr.trans (by exact_mod_cast hmn)

/-- Classical membership in a specified level of the filtration. -/
noncomputable local instance lowerMembershipDecidable
    {G : Type*} [Group G] (F : AntitoneNormalSubgroupFiltration G)
    (n : ℕ) (sigma : G) : Decidable (sigma ∈ F.lower n) :=
  Classical.propDecidable _

/-- The original finite enumeration of an actual subgroup. -/
noncomputable local instance finiteSubgroupFintype
    {G : Type*} [Group G] [Finite G] (H : Subgroup G) : Fintype H :=
  Fintype.ofFinite H

/-- The truncated depth contribution on one interpolation interval of the actual filtration. -/
theorem truncate_depth_eq_intrinsic_summand_of_mem
    {G : Type*} [Group G] [Finite G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1)
    (sigma : F.lower 0) :
    truncateENatAtDVF (depth (sigma : G)) (s + 1) =
      1 + (F.truncatedLowerDepth m sigma : ℝ) +
        (s - m) * (if (sigma : G) ∈ F.lower (m + 1) then 1 else 0) := by
  classical
  let i := depth (sigma : G)
  have hi_one : (1 : ℕ∞) ≤ i := by
    simpa [i] using (hmem 0 (sigma : G)).1 sigma.property
  by_cases hhigh : ((m + 2 : ℕ) : ℕ∞) ≤ i
  · have hsigma : (sigma : G) ∈ F.lower (m + 1) := by
      apply (hmem (m + 1) (sigma : G)).2
      simpa [i, Nat.add_assoc] using hhigh
    have hdepth : F.truncatedLowerDepth m sigma = m := by
      rw [AntitoneNormalSubgroupFiltration.truncatedLowerDepth]
      rw [Finset.filter_eq_self.2]
      · exact Finset.card_range m
      · intro j hj
        apply (hmem (j + 1) (sigma : G)).2
        have hjm : j < m := Finset.mem_range.1 hj
        have hjle : ((j + 2 : ℕ) : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) :=
          ENat.natCast_le_natCast.2 (by omega)
        simpa [i, Nat.add_assoc] using hjle.trans hhigh
    have htrunc : truncateENatAtDVF i (s + 1) = s + 1 := by
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := m + 2) (by
          norm_num [Nat.cast_add, Nat.cast_ofNat] at hsm ⊢
          linarith) hhigh
    rw [htrunc, hdepth, ite_eq_left hsigma, mul_one]
    ring
  · have hlt : i < ((m + 2 : ℕ) : ℕ∞) := lt_of_not_ge hhigh
    have hine : i ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hine
    have hk_one : 1 ≤ k := by
      exact_mod_cast (hi_one.trans_eq hk.symm)
    have hk_upper : k ≤ m + 1 := by
      have : k < m + 2 := by exact_mod_cast (hk.symm ▸ hlt)
      omega
    have hsigma : (sigma : G) ∉ F.lower (m + 1) := by
      intro hsigma
      apply hhigh
      simpa [i, Nat.add_assoc] using (hmem (m + 1) (sigma : G)).1 hsigma
    have hdepth : F.truncatedLowerDepth m sigma = k - 1 := by
      rw [AntitoneNormalSubgroupFiltration.truncatedLowerDepth]
      have hfilter :
          (Finset.range m).filter
              (fun j => (sigma : G) ∈ F.lower (j + 1)) =
            Finset.range (k - 1) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_range]
        have hthreshold :
            ((sigma : G) ∈ F.lower (j + 1)) ↔ j + 2 ≤ k := by
          rw [hmem]
          change (((j + 1 + 1 : ℕ) : ℕ∞) ≤ i) ↔ j + 2 ≤ k
          rw [← hk]
          norm_cast
        rw [hthreshold]
        omega
      rw [hfilter, Finset.card_range]
    have htrunc : truncateENatAtDVF i (s + 1) = k := by
      rw [← hk, truncateENatAtDVF_coe, min_eq_left]
      have : (k : ℝ) ≤ m + 1 := by exact_mod_cast hk_upper
      linarith
    rw [htrunc, hdepth]
    rw [ite_eq_right hsigma]
    simp only [mul_zero, add_zero]
    exact_mod_cast (by omega : k = 1 + (k - 1))

/-- The truncated depth vanishes outside the actual zeroth filtration subgroup. -/
theorem truncate_depth_eq_zero_of_not_mem_lower_zero
    {G : Type*} [Group G] [Finite G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    {s : ℝ} (hs : -1 ≤ s) {sigma : G}
    (hsigma : sigma ∉ F.lower 0) :
    truncateENatAtDVF (depth sigma) (s + 1) = 0 := by
  have hi : depth sigma < 1 := by
    rw [← not_le]
    intro hi
    exact hsigma ((hmem 0 sigma).2 (by simpa using hi))
  have hi0 : depth sigma = 0 := Order.lt_one_iff.1 hi
  rw [hi0]
  calc
    truncateENatAtDVF (0 : ℕ∞) (s + 1) = min (0 : ℝ) (s + 1) := by
      simpa only [ENat.natCast_zero, Nat.cast_zero] using
        truncateENatAtDVF_coe 0 (s + 1)
    _ = 0 := min_eq_left (show (0 : ℝ) ≤ s + 1 by linarith)

/-- The full depth sum is the same sum restricted to the actual zeroth filtration subgroup. -/
theorem sum_truncate_depth_eq_sum_lower_zero_of_mem
    {G : Type*} [Group G] [Fintype G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    {s : ℝ} (hs : -1 ≤ s) :
    (∑ sigma : G, truncateENatAtDVF (depth sigma) (s + 1)) =
      ∑ sigma : F.lower 0,
        truncateENatAtDVF (depth (sigma : G)) (s + 1) := by
  classical
  let q : G → ℝ := fun sigma =>
    truncateENatAtDVF (depth sigma) (s + 1)
  calc
    ∑ sigma : G, q sigma =
        ∑ sigma : G, if sigma ∈ F.lower 0 then q sigma else 0 := by
      apply Finset.sum_congr rfl
      intro sigma _
      by_cases hsigma : sigma ∈ F.lower 0
      · exact (ite_eq_left hsigma).symm
      · rw [ite_eq_right hsigma]
        exact truncate_depth_eq_zero_of_not_mem_lower_zero
          F depth hmem hs hsigma
    _ = ∑ sigma : F.lower 0, q (sigma : G) := by
      rw [← Finset.sum_filter (p := fun sigma : G => sigma ∈ F.lower 0)]
      simpa only [Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter
          (s := (Finset.univ : Finset G)) q
          (p := fun sigma : G => sigma ∈ F.lower 0)).symm

/-- The actual inertia depth sum splits into the constant, truncated-depth and slope terms. -/
theorem sum_lower_zero_truncate_depth_eq_intrinsic_of_mem
    {G : Type*} [Group G] [Finite G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    (m : ℕ) {s : ℝ} (hms : (m : ℝ) ≤ s) (hsm : s ≤ m + 1) :
    (∑ sigma : F.lower 0,
        truncateENatAtDVF (depth (sigma : G)) (s + 1)) =
      Nat.card (F.lower 0) +
        (∑ sigma : F.lower 0, (F.truncatedLowerDepth m sigma : ℝ)) +
        (s - m) * Nat.card (F.lower (m + 1)) := by
  classical
  simp_rw [truncate_depth_eq_intrinsic_summand_of_mem
    F depth hmem m hms hsm]
  have hindicator :
      (∑ sigma : F.lower 0,
        (if (sigma : G) ∈ F.lower (m + 1) then (1 : ℝ) else 0)) =
        Nat.card (F.lower (m + 1)) := by
    exact_mod_cast (F.card_lower_succ_eq_sum_indicator m).symm
  change Finset.sum Finset.univ (fun sigma : F.lower 0 =>
      (1 : ℝ) + (F.truncatedLowerDepth m sigma : ℝ) +
        (s - m) *
          (if (sigma : G) ∈ F.lower (m + 1) then 1 else 0)) = _
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hindicator]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.card_eq_fintype_card]

open _root_.RamificationTheory.DiscreteValuationField.AntitoneNormalSubgroupFiltration
    (herbrandFunction herbrandFunction_of_nonpos) in
/-- The Herbrand function is the normalized sum of the given exact filtration depths. -/
theorem herbrandFunction_eq_depth_sum_of_mem
    {G : Type*} [Group G] [Fintype G]
    (F : AntitoneNormalSubgroupFiltration G) (depth : G → ℕ∞)
    (hmem : ∀ n sigma,
      sigma ∈ F.lower n ↔ (((n + 1 : ℕ) : ℕ∞) ≤ depth sigma))
    {s : ℝ} (hs : -1 ≤ s) :
    (herbrandFunction F) s =
      (1 / Nat.card (F.lower 0) : ℝ) *
        (∑ sigma : G, truncateENatAtDVF (depth sigma) (s + 1)) - 1 := by
  classical
  have hcard : (Nat.card (F.lower 0) : ℝ) ≠ 0 := by
    exact_mod_cast
      (ne_of_gt (show 0 < Nat.card (F.lower 0) from Finite.card_pos))
  rw [sum_truncate_depth_eq_sum_lower_zero_of_mem F depth hmem hs]
  by_cases hs0 : 0 ≤ s
  · let m := ⌊s⌋₊
    have hms : (m : ℝ) ≤ s := Nat.floor_le hs0
    have hsm : s ≤ m + 1 := (Nat.lt_floor_add_one s).le
    rw [sum_lower_zero_truncate_depth_eq_intrinsic_of_mem
      F depth hmem m hms hsm]
    rw [F.herbrandFunction_eq_depth_sum_of_mem_Icc m hms hsm]
    field_simp
    ring
  · have hsle : s ≤ 0 := le_of_not_ge hs0
    rw [(herbrandFunction_of_nonpos F) hsle]
    have hpoint : ∀ sigma : F.lower 0,
        truncateENatAtDVF (depth (sigma : G)) (s + 1) = s + 1 := by
      intro sigma
      have hi : (1 : ℕ∞) ≤ depth (sigma : G) := by
        exact (hmem 0 (sigma : G)).1 sigma.property
      exact truncateENatAtDVF_eq_right_of_natCast_le
        (m := 1) (by
          norm_num at hsle ⊢
          linarith) hi
    simp_rw [hpoint]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    field_simp
    ring

end Higher
end RamificationTheory.HilbertRamification
