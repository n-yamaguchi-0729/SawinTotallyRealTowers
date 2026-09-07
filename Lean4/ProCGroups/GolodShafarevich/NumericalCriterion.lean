import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
/-!
# Numerical Golod--Shafarevich criterion

This file isolates the numerical argument used after the truncated
Golod--Shafarevich coefficient inequality.  A zero-extended backwards shift
makes every coefficient statement safe in `ℕ`.  Abel summation turns the
coefficient inequalities into positivity of the Golod--Shafarevich
polynomial on `[0, 1)`, while eventual stabilization handles the endpoint
`t = 1` separately.

The final theorem is deliberately assumption-level: it consumes only a
monotone bounded dimension sequence, the truncated inequalities, relator
depths, and positivity of the generator count.
-/

open scoped BigOperators

namespace ClassFieldTower.ProP

/-- The zero-extended backwards shift used in a truncated coefficient
inequality. -/
def backshift (A : ℕ → ℕ) (N k : ℕ) : ℕ :=
  if k ≤ N then A (N - k) else 0

@[simp]
theorem backshift_add (A : ℕ → ℕ) (n k : ℕ) :
    backshift A (n + k) k = A n := by
  simp [backshift]

theorem backshift_lt (A : ℕ → ℕ) {n k : ℕ} (h : n < k) :
    backshift A n k = 0 := by
  simp [backshift, Nat.not_le.mpr h]

section Abel

variable (A : ℕ → ℕ) (C : ℕ)

/-- A uniformly bounded sequence has a summable weighted series on
`[0, 1)`. -/
theorem weighted_summable
    (hAC : ∀ n, A n ≤ C) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable (fun n : ℕ ↦ (A n : ℝ) * t ^ n) := by
  apply Summable.of_nonneg_of_le (f := fun n : ℕ ↦ (C : ℝ) * t ^ n)
  · intro n
    positivity
  · intro n
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hAC n) (pow_nonneg ht0 n)
  · exact (summable_geometric_of_lt_one ht0 ht1).mul_left (C : ℝ)

/-- Abel summation for a zero-extended backwards shift. -/
theorem weighted_backshift_hasSum
    (hAC : ∀ n, A n ≤ C) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℕ) :
    HasSum (fun n : ℕ ↦ (backshift A n k : ℝ) * t ^ n)
      (t ^ k * ∑' n : ℕ, (A n : ℝ) * t ^ n) := by
  let f : ℕ → ℝ := fun n ↦ (backshift A n k : ℝ) * t ^ n
  have hprefix : ∑ i ∈ Finset.range k, f i = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [f, backshift, Nat.not_le.mpr (Finset.mem_range.mp hi)]
  rw [← hasSum_nat_add_iff' k]
  rw [hprefix, sub_zero]
  have hsum :=
    (weighted_summable A C hAC ht0 ht1).hasSum.mul_left (t ^ k)
  have hfun : (fun n ↦ f (n + k)) =
      fun n ↦ t ^ k * ((A n : ℝ) * t ^ n) := by
    funext n
    simp only [f, backshift_add]
    rw [pow_add]
    ring
  rw [hfun]
  exact hsum

/-- The sum of a weighted backwards shift is the correspondingly shifted
generating series. -/
theorem tsum_weighted_backshift
    (hAC : ∀ n, A n ≤ C) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (k : ℕ) :
    ∑' n : ℕ, (backshift A n k : ℝ) * t ^ n =
      t ^ k * ∑' n : ℕ, (A n : ℝ) * t ^ n :=
  (weighted_backshift_hasSum A C hAC ht0 ht1 k).tsum_eq

end Abel

/-- The Nat-safe truncated coefficient inequalities force positivity of the
Golod--Shafarevich polynomial at every real `t` in `[0, 1)`, provided the
dimension sequence is uniformly bounded and nonzero in degree zero. -/
theorem gsPolynomial_pos_of_truncated
    {d r : ℕ} (ν : Fin r → ℕ) (A : ℕ → ℕ)
    (hbound : ∃ C, ∀ n, A n ≤ C)
    (hA0 : 0 < A 0)
    (hineq : ∀ N,
      1 + d * backshift A N 1 ≤
        A N + ∑ i : Fin r, backshift A N (ν i))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    0 < 1 - d * t + ∑ i : Fin r, t ^ ν i := by
  obtain ⟨C, hC⟩ := hbound
  let S : ℝ := ∑' n : ℕ, (A n : ℝ) * t ^ n
  have hsumA : Summable (fun n : ℕ ↦ (A n : ℝ) * t ^ n) :=
    weighted_summable A C hC ht0 ht1
  have hSpos : 0 < S := by
    have hterm0 : 0 < (A 0 : ℝ) * t ^ 0 := by
      simpa using (show (0 : ℝ) < A 0 by exact_mod_cast hA0)
    exact hsumA.tsum_pos (fun n ↦ by positivity) 0 hterm0
  have hleft : Summable (fun N : ℕ ↦
      ((1 : ℝ) + d * backshift A N 1) * t ^ N) := by
    have hgeom := summable_geometric_of_lt_one ht0 ht1
    have hs := (weighted_backshift_hasSum A C hC ht0 ht1 1).summable
    simpa [add_mul, mul_assoc] using hgeom.add (hs.mul_left (d : ℝ))
  have hright : Summable (fun N : ℕ ↦
      ((A N : ℝ) + ∑ i : Fin r, backshift A N (ν i)) * t ^ N) := by
    have hs : Summable (fun N : ℕ ↦
        ∑ i : Fin r, (backshift A N (ν i) : ℝ) * t ^ N) :=
      summable_sum (s := (Finset.univ : Finset (Fin r))) fun i _ ↦
        (weighted_backshift_hasSum A C hC ht0 ht1 (ν i)).summable
    simpa [add_mul, Finset.sum_mul] using hsumA.add hs
  have htsum :
      ∑' N : ℕ, ((1 : ℝ) + d * backshift A N 1) * t ^ N ≤
        ∑' N : ℕ, ((A N : ℝ) + ∑ i : Fin r, backshift A N (ν i)) * t ^ N := by
    apply hleft.tsum_le_tsum _ hright
    intro N
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg ht0 N)
    exact_mod_cast hineq N
  have hgeom : ∑' n : ℕ, t ^ n = (1 - t)⁻¹ :=
    tsum_geometric_of_lt_one ht0 ht1
  have hshift (k : ℕ) :
      ∑' n : ℕ, (backshift A n k : ℝ) * t ^ n = t ^ k * S :=
    tsum_weighted_backshift A C hC ht0 ht1 k
  have hgeomSum : Summable (fun n : ℕ ↦ t ^ n) :=
    summable_geometric_of_lt_one ht0 ht1
  have hback1 : Summable (fun n : ℕ ↦
      (d : ℝ) * ((backshift A n 1 : ℝ) * t ^ n)) :=
    (weighted_backshift_hasSum A C hC ht0 ht1 1).summable.mul_left (d : ℝ)
  have hleftEval :
      ∑' N : ℕ, ((1 : ℝ) + d * backshift A N 1) * t ^ N =
        (1 - t)⁻¹ + (d : ℝ) * (t * S) := by
    calc
      _ = ∑' N : ℕ, (t ^ N +
          (d : ℝ) * ((backshift A N 1 : ℝ) * t ^ N)) := by
            apply tsum_congr
            intro N
            ring
      _ = (∑' N : ℕ, t ^ N) +
          ∑' N : ℕ, (d : ℝ) * ((backshift A N 1 : ℝ) * t ^ N) :=
            hgeomSum.tsum_add hback1
      _ = _ := by
        rw [hgeom,
          (weighted_backshift_hasSum A C hC ht0 ht1 1).summable.tsum_mul_left (d : ℝ),
          hshift 1]
        simp
  have hshiftFamily : Summable (fun N : ℕ ↦
      ∑ i : Fin r, (backshift A N (ν i) : ℝ) * t ^ N) :=
    summable_sum (s := (Finset.univ : Finset (Fin r))) fun i _ ↦
      (weighted_backshift_hasSum A C hC ht0 ht1 (ν i)).summable
  have hrightEval :
      ∑' N : ℕ, ((A N : ℝ) + ∑ i : Fin r, backshift A N (ν i)) * t ^ N =
        S + ∑ i : Fin r, t ^ ν i * S := by
    calc
      _ = ∑' N : ℕ, ((A N : ℝ) * t ^ N +
          ∑ i : Fin r, (backshift A N (ν i) : ℝ) * t ^ N) := by
            apply tsum_congr
            intro N
            simp only [add_mul, Finset.sum_mul, Nat.cast_sum]
      _ = S + ∑' N : ℕ,
          ∑ i : Fin r, (backshift A N (ν i) : ℝ) * t ^ N :=
            hsumA.tsum_add hshiftFamily
      _ = _ := by
        congr 1
        rw [Summable.tsum_finsetSum (fun i _ ↦
          (weighted_backshift_hasSum A C hC ht0 ht1 (ν i)).summable)]
        apply Finset.sum_congr rfl
        intro i _
        exact hshift (ν i)
  have hab : (1 - t)⁻¹ + (d : ℝ) * (t * S) ≤
      S + ∑ i : Fin r, t ^ ν i * S := by
    rw [← hleftEval, ← hrightEval]
    exact htsum
  have hone : 0 < (1 - t)⁻¹ := by
    positivity
  have hmul : (1 - t)⁻¹ ≤
      (1 - d * t + ∑ i : Fin r, t ^ ν i) * S := by
    have haux : (1 - t)⁻¹ ≤
        S + ∑ i : Fin r, t ^ ν i * S - (d : ℝ) * (t * S) := by
      linarith [hab]
    calc
      (1 - t)⁻¹ ≤ S + ∑ i : Fin r, t ^ ν i * S - (d : ℝ) * (t * S) := haux
      _ = (1 - d * t + ∑ i : Fin r, t ^ ν i) * S := by
        rw [← Finset.sum_mul]
        ring
  nlinarith

/-- A backwards shift of a monotone sequence is bounded by the unshifted
term. -/
theorem backshift_le_of_monotone {A : ℕ → ℕ} (hA : Monotone A) (N k : ℕ) :
    backshift A N k ≤ A N := by
  unfold backshift
  split_ifs
  · exact hA (Nat.sub_le N k)
  · exact Nat.zero_le _

/-- The `t = 1` boundary calculation.  Eventual stabilization supplies a
coefficient where the constant term in the truncated inequality forces
`d ≤ r`. -/
theorem generator_le_relation_of_stable_truncated
    {d r : ℕ} (ν : Fin r → ℕ) (A : ℕ → ℕ)
    (hmono : Monotone A) (hA0 : 0 < A 0)
    (hstable : ∃ M, ∀ n, M ≤ n → A n = A M)
    (hineq : ∀ N,
      1 + d * backshift A N 1 ≤
        A N + ∑ i : Fin r, backshift A N (ν i)) :
    d ≤ r := by
  obtain ⟨M, hM⟩ := hstable
  let N := M + 1
  have hMN : M ≤ N := by simp [N]
  have hAN : A N = A M := hM N hMN
  have hshiftOne : backshift A N 1 = A M := by
    simp [N, backshift]
  have hANpos : 0 < A N := by
    rw [hAN]
    exact lt_of_lt_of_le hA0 (hmono (Nat.zero_le M))
  have hsum : ∑ i : Fin r, backshift A N (ν i) ≤ r * A N := by
    calc
      _ ≤ ∑ _i : Fin r, A N :=
        Finset.sum_le_sum fun i _ ↦ backshift_le_of_monotone hmono N (ν i)
      _ = r * A N := by simp
  have hmain : 1 + d * A N ≤ A N + r * A N := by
    calc
      1 + d * A N = 1 + d * backshift A N 1 := by rw [hshiftOne, hAN]
      _ ≤ A N + ∑ i : Fin r, backshift A N (ν i) := hineq N
      _ ≤ A N + r * A N := Nat.add_le_add_left hsum _
  have hlt : d * A N < (r + 1) * A N := by
    calc
      d * A N < 1 + d * A N := by omega
      _ ≤ A N + r * A N := hmain
      _ = (r + 1) * A N := by simp [Nat.add_mul, Nat.add_comm]
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_right hlt)

/-- Assumption-level numerical endpoint for the truncated
Golod--Shafarevich argument. -/
theorem square_generator_lt_four_relations_of_truncated
    {d r : ℕ} (ν : Fin r → ℕ) (A : ℕ → ℕ)
    (hmono : Monotone A) (hbound : ∃ C, ∀ n, A n ≤ C)
    (hineq : ∀ N,
      1 + d * backshift A N 1 ≤
        A N + ∑ i : Fin r, backshift A N (ν i))
    (hdepth : ∀ i, 2 ≤ ν i) (hd : 0 < d) :
    d ^ 2 < 4 * r := by
  have hA0 : 0 < A 0 := by
    have hν0 (i : Fin r) : ¬ν i ≤ 0 := by
      have := hdepth i
      omega
    have h : 1 ≤ A 0 := by
      simpa [backshift, hν0] using hineq 0
    omega
  obtain ⟨C, hC⟩ := hbound
  have hstable : ∃ M, ∀ n, M ≤ n → A n = A M := by
    obtain ⟨b, M, hM⟩ := converges_of_monotone_of_bounded hmono hC
    exact ⟨M, fun n hn ↦ (hM n hn).trans (hM M le_rfl).symm⟩
  have hdr : d ≤ r :=
    generator_le_relation_of_stable_truncated ν A hmono hA0 hstable hineq
  by_cases hd2 : d ≤ 2
  · nlinarith
  · have hd3 : 3 ≤ d := by omega
    let t : ℝ := 2 / (d : ℝ)
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have ht0 : (0 : ℝ) ≤ t := by positivity
    have ht1 : t < 1 := by
      dsimp [t]
      rw [div_lt_one hdR]
      exact_mod_cast hd3
    have hpoly : 0 < 1 - d * t + ∑ i : Fin r, t ^ ν i :=
      gsPolynomial_pos_of_truncated ν A ⟨C, hC⟩ hA0 hineq ht0 ht1
    have htOne : t ≤ 1 := ht1.le
    have hsum : ∑ i : Fin r, t ^ ν i ≤ r * t ^ 2 := by
      calc
        _ ≤ ∑ _i : Fin r, t ^ 2 :=
          Finset.sum_le_sum fun i _ ↦ pow_le_pow_of_le_one ht0 htOne (hdepth i)
        _ = r * t ^ 2 := by simp
    have hquad : 0 < 1 - (d : ℝ) * t + (r : ℝ) * t ^ 2 :=
      lt_of_lt_of_le hpoly (by gcongr)
    have hidentity :
        (1 - (d : ℝ) * t + (r : ℝ) * t ^ 2) * (d : ℝ) ^ 2 =
          (4 : ℝ) * (r : ℝ) - (d : ℝ) ^ 2 := by
      dsimp [t]
      field_simp
      ring
    have hreal : (d : ℝ) ^ 2 < (4 : ℝ) * (r : ℝ) := by
      have hsq : (0 : ℝ) < (d : ℝ) ^ 2 := sq_pos_of_pos hdR
      nlinarith [mul_pos hquad hsq]
    exact_mod_cast hreal

end ClassFieldTower.ProP
