/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Index calculus for the tame Abhyankar frontier

The geometric input of tame Abhyankar is a source theorem bounding the
ramification index after base change by `e / gcd e e'`.  This file proves the
arithmetic consequences of that bound.  It deliberately does not assert the
geometric bound itself.
-/

noncomputable section

namespace TameAbhyankar

/-- The index bound supplied by the geometric tame-base-change step: the
ramification index after base change divides `e / gcd e e'`. -/
def AbhyankarIndexBound (e baseChangeRamificationIndex newRamificationIndex : ℕ) :
    Prop :=
  newRamificationIndex ∣ e / Nat.gcd e baseChangeRamificationIndex

theorem div_gcd_eq_one_of_dvd {e baseChangeRamificationIndex : ℕ}
    (he : 0 < e) (hdiv : e ∣ baseChangeRamificationIndex) :
    e / Nat.gcd e baseChangeRamificationIndex = 1 := by
  rw [Nat.gcd_eq_left hdiv, Nat.div_self he]

/-- Dividing the lcm by the right input removes exactly the common gcd from
the left input.  This is the arithmetic shape of the value-group computation
behind tame Abhyankar. -/
theorem lcm_div_right_eq_div_gcd {e baseChangeRamificationIndex : ℕ}
    (hbase : 0 < baseChangeRamificationIndex) :
    Nat.lcm e baseChangeRamificationIndex / baseChangeRamificationIndex =
      e / Nat.gcd e baseChangeRamificationIndex := by
  calc
    Nat.lcm e baseChangeRamificationIndex /
        baseChangeRamificationIndex =
        (e * baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex) /
            baseChangeRamificationIndex := by
      rfl
    _ = (e * (baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex)) /
            baseChangeRamificationIndex := by
      rw [Nat.mul_div_assoc e
        (Nat.gcd_dvd_right e baseChangeRamificationIndex)]
    _ =
        ((baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex) * e) /
            ((baseChangeRamificationIndex /
              Nat.gcd e baseChangeRamificationIndex) *
                Nat.gcd e baseChangeRamificationIndex) := by
      rw [Nat.mul_comm e
        (baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex),
        Nat.div_mul_cancel
          (Nat.gcd_dvd_right e baseChangeRamificationIndex)]
    _ = e / Nat.gcd e baseChangeRamificationIndex := by
      rw [Nat.mul_div_mul_left]
      exact Nat.div_pos
        (Nat.le_of_dvd hbase
          (Nat.gcd_dvd_right e baseChangeRamificationIndex))
        (Nat.gcd_pos_of_pos_right e hbase)

/-- If a tower/value-group computation identifies
`baseChangeRamificationIndex * newRamificationIndex` with the lcm of the two
lower ramification indices, the tame Abhyankar index bound follows by pure
arithmetic. -/
theorem abhyankarIndexBound_of_mul_eq_lcm
    {e baseChangeRamificationIndex newRamificationIndex : ℕ}
    (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        Nat.lcm e baseChangeRamificationIndex) :
    AbhyankarIndexBound e baseChangeRamificationIndex
      newRamificationIndex := by
  have hnew :
      newRamificationIndex =
        Nat.lcm e baseChangeRamificationIndex /
          baseChangeRamificationIndex := by
    rw [← hprod,
      Nat.mul_div_right newRamificationIndex hbase]
  rw [AbhyankarIndexBound,
    ← lcm_div_right_eq_div_gcd (e := e) hbase, ← hnew]

/-- Divisibility form of the lcm source: it is enough for
`baseChangeRamificationIndex * newRamificationIndex` to divide the lcm of the
two lower ramification indices. -/
theorem abhyankarIndexBound_of_mul_dvd_lcm
    {e baseChangeRamificationIndex newRamificationIndex : ℕ}
    (hbase : 0 < baseChangeRamificationIndex)
    (hprod_dvd :
      baseChangeRamificationIndex * newRamificationIndex ∣
        Nat.lcm e baseChangeRamificationIndex) :
    AbhyankarIndexBound e baseChangeRamificationIndex
      newRamificationIndex := by
  rcases hprod_dvd with ⟨q, hq⟩
  rw [AbhyankarIndexBound,
    ← lcm_div_right_eq_div_gcd (e := e) hbase]
  refine ⟨q, ?_⟩
  rw [hq, mul_assoc, Nat.mul_div_right _ hbase]

/-- If the lcm of two value steps divides `a * c`, the primitive part of the
second step after removing the common gcd with `a` divides `c`. -/
theorem div_gcd_dvd_of_lcm_dvd_mul_left {a b c : ℕ}
    (ha : 0 < a) (hdiv : Nat.lcm a b ∣ a * c) :
    b / Nat.gcd a b ∣ c := by
  have hquot : Nat.lcm a b / a ∣ c := by
    rcases hdiv with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left ha
    have hlcm :
        a * (Nat.lcm a b / a) = Nat.lcm a b := by
      rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.dvd_lcm_left a b)]
    calc
      a * c = Nat.lcm a b * q := hq
      _ = (a * (Nat.lcm a b / a)) * q := by
        rw [hlcm]
      _ = a * ((Nat.lcm a b / a) * q) := by
        rw [mul_assoc]
  have hrewrite :
      Nat.lcm a b / a = b / Nat.gcd a b := by
    simpa [Nat.lcm_comm, Nat.gcd_comm] using
      (lcm_div_right_eq_div_gcd
        (e := b) (baseChangeRamificationIndex := a) ha)
  simpa [hrewrite] using hquot

/-- In a ramification square product, the primitive part of the left lower
index divides the right upper branch.  This is the unavoidable arithmetic
content of the square before the tame/value-group input removes the remaining
common quotient. -/
theorem div_gcd_dvd_right_of_mul_eq_mul
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex) :
    e / Nat.gcd e baseChangeRamificationIndex ∣
      newRamificationIndex := by
  let g := Nat.gcd e baseChangeRamificationIndex
  have hg_pos : 0 < g :=
    Nat.gcd_pos_of_pos_left baseChangeRamificationIndex he
  have hcop :
      Nat.Coprime (e / g) (baseChangeRamificationIndex / g) := by
    simpa [g] using
      (Nat.coprime_div_gcd_div_gcd
        (m := e) (n := baseChangeRamificationIndex) hg_pos)
  have hcancel :
      (baseChangeRamificationIndex / g) * newRamificationIndex =
        (e / g) * leftBaseChangedIndex := by
    apply Nat.eq_of_mul_eq_mul_right hg_pos
    calc
      ((baseChangeRamificationIndex / g) *
          newRamificationIndex) * g =
          (baseChangeRamificationIndex / g * g) *
            newRamificationIndex := by
        ac_rfl
      _ =
          baseChangeRamificationIndex * newRamificationIndex := by
        rw [Nat.div_mul_cancel
          (Nat.gcd_dvd_right e baseChangeRamificationIndex)]
      _ = e * leftBaseChangedIndex := hprod
      _ =
          (e / g * g) * leftBaseChangedIndex := by
        rw [Nat.div_mul_cancel
          (Nat.gcd_dvd_left e baseChangeRamificationIndex)]
      _ = ((e / g) * leftBaseChangedIndex) * g := by
        ac_rfl
  have hdvd_mul :
      e / g ∣
        (baseChangeRamificationIndex / g) *
          newRamificationIndex := by
    rw [hcancel]
    exact dvd_mul_right _ _
  simpa [g] using hcop.dvd_of_dvd_mul_left hdvd_mul

/-- Symmetric primitive-part divisibility for the other upper branch of a
ramification square product. -/
theorem div_gcd_dvd_left_of_mul_eq_mul
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex) :
    baseChangeRamificationIndex / Nat.gcd e baseChangeRamificationIndex ∣
      leftBaseChangedIndex := by
  have hprod' :
      e * leftBaseChangedIndex =
        baseChangeRamificationIndex * newRamificationIndex := hprod.symm
  simpa [Nat.gcd_comm, mul_comm] using
    (div_gcd_dvd_right_of_mul_eq_mul
      (e := baseChangeRamificationIndex)
      (baseChangeRamificationIndex := e)
      (newRamificationIndex := leftBaseChangedIndex)
      (leftBaseChangedIndex := newRamificationIndex)
      hbase hprod')

/-- A ramification square product factors both upper branches through the
primitive lower ramification indices and a single common quotient.  The tame
Abhyankar value-group step is precisely the source that must force this common
quotient to be `1`. -/
theorem exists_commonPrimitiveQuotient_of_mul_eq_mul
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex) :
    ∃ commonQuotient,
      newRamificationIndex =
          (e / Nat.gcd e baseChangeRamificationIndex) *
            commonQuotient ∧
        leftBaseChangedIndex =
          (baseChangeRamificationIndex /
            Nat.gcd e baseChangeRamificationIndex) *
              commonQuotient := by
  let g := Nat.gcd e baseChangeRamificationIndex
  have hg_pos : 0 < g :=
    Nat.gcd_pos_of_pos_left baseChangeRamificationIndex he
  have hleftPrimitive_pos :
      0 < e / g :=
    Nat.div_pos
      (Nat.le_of_dvd he
        (Nat.gcd_dvd_left e baseChangeRamificationIndex))
      hg_pos
  have hbasePrimitive_pos :
      0 < baseChangeRamificationIndex / g :=
    Nat.div_pos
      (Nat.le_of_dvd hbase
        (Nat.gcd_dvd_right e baseChangeRamificationIndex))
      hg_pos
  have hcancel :
      (baseChangeRamificationIndex / g) * newRamificationIndex =
        (e / g) * leftBaseChangedIndex := by
    apply Nat.eq_of_mul_eq_mul_right hg_pos
    calc
      ((baseChangeRamificationIndex / g) *
          newRamificationIndex) * g =
          (baseChangeRamificationIndex / g * g) *
            newRamificationIndex := by
        ac_rfl
      _ =
          baseChangeRamificationIndex * newRamificationIndex := by
        rw [Nat.div_mul_cancel
          (Nat.gcd_dvd_right e baseChangeRamificationIndex)]
      _ = e * leftBaseChangedIndex := hprod
      _ =
          (e / g * g) * leftBaseChangedIndex := by
        rw [Nat.div_mul_cancel
          (Nat.gcd_dvd_left e baseChangeRamificationIndex)]
      _ = ((e / g) * leftBaseChangedIndex) * g := by
        ac_rfl
  rcases div_gcd_dvd_right_of_mul_eq_mul he hprod with
    ⟨rightQuotient, hrightQuotient⟩
  rcases div_gcd_dvd_left_of_mul_eq_mul hbase hprod with
    ⟨leftQuotient, hleftQuotient⟩
  have hquotient_eq : rightQuotient = leftQuotient := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos hleftPrimitive_pos hbasePrimitive_pos)
    calc
      (e / g * (baseChangeRamificationIndex / g)) *
          rightQuotient =
          (baseChangeRamificationIndex / g) *
            ((e / g) * rightQuotient) := by
        ac_rfl
      _ =
          (baseChangeRamificationIndex / g) *
            newRamificationIndex := by
        rw [hrightQuotient]
      _ =
          (e / g) * leftBaseChangedIndex := hcancel
      _ =
          (e / g) *
            ((baseChangeRamificationIndex / g) *
              leftQuotient) := by
        rw [hleftQuotient]
      _ =
          (e / g * (baseChangeRamificationIndex / g)) *
            leftQuotient := by
        ac_rfl
  refine ⟨rightQuotient, ?_, ?_⟩
  · simpa [g] using hrightQuotient
  · rw [hleftQuotient, ← hquotient_eq]

/-- In a ramification square product, the two upper branches are primitive at
the same time: both are obtained from their primitive lower parts by the same
common quotient.  This isolates the arithmetic point that forcing the common
quotient to be `1` can be checked on either upper branch. -/
theorem right_eq_div_gcd_iff_left_eq_div_gcd_of_mul_eq_mul
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : Nat}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex) :
    Iff
      (newRamificationIndex =
        e / Nat.gcd e baseChangeRamificationIndex)
      (leftBaseChangedIndex =
        baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex) := by
  let g := Nat.gcd e baseChangeRamificationIndex
  have hg_pos : 0 < g :=
    Nat.gcd_pos_of_pos_left baseChangeRamificationIndex he
  have hleftPrimitive_pos : 0 < e / g :=
    Nat.div_pos
      (Nat.le_of_dvd he
        (Nat.gcd_dvd_left e baseChangeRamificationIndex))
      hg_pos
  have hbasePrimitive_pos : 0 < baseChangeRamificationIndex / g :=
    Nat.div_pos
      (Nat.le_of_dvd hbase
        (Nat.gcd_dvd_right e baseChangeRamificationIndex))
      hg_pos
  rcases exists_commonPrimitiveQuotient_of_mul_eq_mul
      he hbase hprod with
    ⟨commonQuotient, hnew, hleft⟩
  constructor
  · intro hnewPrimitive
    have hcommon : commonQuotient = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hleftPrimitive_pos
      calc
        (e / g) * commonQuotient = newRamificationIndex := by
          simpa [g] using hnew.symm
        _ = e / g := by
          simpa [g] using hnewPrimitive
        _ = (e / g) * 1 := by
          rw [mul_one]
    rw [hleft, hcommon, mul_one]
  · intro hleftPrimitive
    have hcommon : commonQuotient = 1 := by
      apply Nat.eq_of_mul_eq_mul_left hbasePrimitive_pos
      calc
        (baseChangeRamificationIndex / g) * commonQuotient =
            leftBaseChangedIndex := by
          simpa [g] using hleft.symm
        _ = baseChangeRamificationIndex / g := by
          simpa [g] using hleftPrimitive
        _ = (baseChangeRamificationIndex / g) * 1 := by
          rw [mul_one]
    rw [hnew, hcommon, mul_one]

/-- Contrapositive form of
`right_eq_div_gcd_iff_left_eq_div_gcd_of_mul_eq_mul`, useful for moving a
non-primitive obstruction between the two upper branches without introducing a
new branch-coprimality assumption. -/
theorem right_ne_div_gcd_iff_left_ne_div_gcd_of_mul_eq_mul
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : Nat}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex) :
    Iff
      (Not (newRamificationIndex =
        e / Nat.gcd e baseChangeRamificationIndex))
      (Not (leftBaseChangedIndex =
        baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex)) := by
  have hiff :=
    right_eq_div_gcd_iff_left_eq_div_gcd_of_mul_eq_mul
      he hbase hprod
  constructor
  · intro hnew_ne hleft_eq
    exact hnew_ne (hiff.mpr hleft_eq)
  · intro hleft_ne hnew_eq
    exact hleft_ne (hiff.mp hnew_eq)

/-- If the right upper branch of a ramification square is bounded by the left
lower index, then the common primitive quotient is bounded by the lower gcd. -/
theorem exists_commonPrimitiveQuotient_le_gcd_of_mul_eq_mul_of_right_le
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hnew_le : newRamificationIndex ≤ e) :
    ∃ commonQuotient,
      newRamificationIndex =
          (e / Nat.gcd e baseChangeRamificationIndex) *
            commonQuotient ∧
        leftBaseChangedIndex =
          (baseChangeRamificationIndex /
            Nat.gcd e baseChangeRamificationIndex) *
              commonQuotient ∧
        commonQuotient ≤ Nat.gcd e baseChangeRamificationIndex := by
  let g := Nat.gcd e baseChangeRamificationIndex
  have hg_pos : 0 < g :=
    Nat.gcd_pos_of_pos_left baseChangeRamificationIndex he
  have hleftPrimitive_pos : 0 < e / g :=
    Nat.div_pos
      (Nat.le_of_dvd he
        (Nat.gcd_dvd_left e baseChangeRamificationIndex))
      hg_pos
  rcases exists_commonPrimitiveQuotient_of_mul_eq_mul
      he hbase hprod with
    ⟨commonQuotient, hnew, hleft⟩
  have hcommon_le : commonQuotient ≤ g := by
    exact Nat.le_of_mul_le_mul_left
      (by
        calc
          (e / g) * commonQuotient =
              newRamificationIndex := by
            simpa [g] using hnew.symm
          _ ≤ e := hnew_le
          _ = (e / g) * g := by
            simpa [g] using
              (Nat.div_mul_cancel
                (Nat.gcd_dvd_left e baseChangeRamificationIndex)).symm)
      hleftPrimitive_pos
  exact ⟨commonQuotient, hnew, hleft, by simpa [g] using hcommon_le⟩

/-- Symmetric bound for the common primitive quotient, using the left upper
branch bound by the right lower index. -/
theorem exists_commonPrimitiveQuotient_le_gcd_of_mul_eq_mul_of_left_le
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hleft_le : leftBaseChangedIndex ≤ baseChangeRamificationIndex) :
    ∃ commonQuotient,
      newRamificationIndex =
          (e / Nat.gcd e baseChangeRamificationIndex) *
            commonQuotient ∧
        leftBaseChangedIndex =
          (baseChangeRamificationIndex /
            Nat.gcd e baseChangeRamificationIndex) *
              commonQuotient ∧
        commonQuotient ≤ Nat.gcd e baseChangeRamificationIndex := by
  let g := Nat.gcd e baseChangeRamificationIndex
  have hg_pos : 0 < g :=
    Nat.gcd_pos_of_pos_right e hbase
  have hbasePrimitive_pos : 0 < baseChangeRamificationIndex / g :=
    Nat.div_pos
      (Nat.le_of_dvd hbase
        (Nat.gcd_dvd_right e baseChangeRamificationIndex))
      hg_pos
  rcases exists_commonPrimitiveQuotient_of_mul_eq_mul
      he hbase hprod with
    ⟨commonQuotient, hnew, hleft⟩
  have hcommon_le : commonQuotient ≤ g := by
    exact Nat.le_of_mul_le_mul_left
      (by
        calc
          (baseChangeRamificationIndex / g) * commonQuotient =
              leftBaseChangedIndex := by
            simpa [g] using hleft.symm
          _ ≤ baseChangeRamificationIndex := hleft_le
          _ = (baseChangeRamificationIndex / g) * g := by
            simpa [g] using
              (Nat.div_mul_cancel
                (Nat.gcd_dvd_right e baseChangeRamificationIndex)).symm)
      hbasePrimitive_pos
  exact ⟨commonQuotient, hnew, hleft, by simpa [g] using hcommon_le⟩

/-- A non-primitive right upper branch exposes a common prime divisor of the
two upper branches. -/
theorem exists_prime_commonPrimitiveObstruction_of_mul_eq_mul_of_right_le_of_ne
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hnew_le : newRamificationIndex ≤ e)
    (hnew_ne :
      newRamificationIndex ≠ e / Nat.gcd e baseChangeRamificationIndex) :
    ∃ commonQuotient,
      commonQuotient ≤ Nat.gcd e baseChangeRamificationIndex ∧
        newRamificationIndex =
          (e / Nat.gcd e baseChangeRamificationIndex) * commonQuotient ∧
        leftBaseChangedIndex =
          (baseChangeRamificationIndex /
            Nat.gcd e baseChangeRamificationIndex) * commonQuotient ∧
        ∃ p, Nat.Prime p ∧ p ∣ commonQuotient ∧
          p ∣ newRamificationIndex ∧ p ∣ leftBaseChangedIndex := by
  rcases exists_commonPrimitiveQuotient_le_gcd_of_mul_eq_mul_of_right_le
      he hbase hprod hnew_le with
    ⟨commonQuotient, hnew, hleft, hcommon_le⟩
  have hcommon_ne : commonQuotient ≠ 1 := by
    intro hcommon
    apply hnew_ne
    rw [hnew, hcommon, mul_one]
  rcases Nat.exists_prime_and_dvd hcommon_ne with
    ⟨p, hp, hp_dvd_common⟩
  refine ⟨commonQuotient, hcommon_le, hnew, hleft, p, hp,
    hp_dvd_common, ?_, ?_⟩
  · rw [hnew]
    exact dvd_mul_of_dvd_right hp_dvd_common _
  · rw [hleft]
    exact dvd_mul_of_dvd_right hp_dvd_common _

/-- Symmetric prime obstruction extracted from the left upper branch. -/
theorem exists_prime_commonPrimitiveObstruction_of_mul_eq_mul_of_left_le_of_ne
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hleft_le : leftBaseChangedIndex ≤ baseChangeRamificationIndex)
    (hleft_ne :
      leftBaseChangedIndex ≠
        baseChangeRamificationIndex /
          Nat.gcd e baseChangeRamificationIndex) :
    ∃ commonQuotient,
      commonQuotient ≤ Nat.gcd e baseChangeRamificationIndex ∧
        newRamificationIndex =
          (e / Nat.gcd e baseChangeRamificationIndex) *
            commonQuotient ∧
        leftBaseChangedIndex =
          (baseChangeRamificationIndex /
            Nat.gcd e baseChangeRamificationIndex) *
              commonQuotient ∧
        ∃ p, Nat.Prime p ∧ p ∣ commonQuotient ∧
          p ∣ newRamificationIndex ∧ p ∣ leftBaseChangedIndex := by
  rcases exists_commonPrimitiveQuotient_le_gcd_of_mul_eq_mul_of_left_le
      he hbase hprod hleft_le with
    ⟨commonQuotient, hnew, hleft, hcommon_le⟩
  have hcommon_ne : commonQuotient ≠ 1 := by
    intro hcommon
    apply hleft_ne
    rw [hleft, hcommon, mul_one]
  rcases Nat.exists_prime_and_dvd hcommon_ne with
    ⟨p, hp, hp_dvd_common⟩
  refine ⟨commonQuotient, hcommon_le, hnew, hleft, p, hp,
    hp_dvd_common, ?_, ?_⟩
  · rw [hnew]
    exact dvd_mul_of_dvd_right hp_dvd_common _
  · rw [hleft]
    exact dvd_mul_of_dvd_right hp_dvd_common _

/-- Symmetric obstruction elimination for the left upper branch. -/
theorem left_eq_div_gcd_of_mul_eq_mul_of_left_le_of_coprime
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (he : 0 < e) (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hleft_le : leftBaseChangedIndex ≤ baseChangeRamificationIndex)
    (hcop : Nat.Coprime newRamificationIndex leftBaseChangedIndex) :
    leftBaseChangedIndex =
      baseChangeRamificationIndex /
        Nat.gcd e baseChangeRamificationIndex := by
  by_contra hne
  rcases exists_prime_commonPrimitiveObstruction_of_mul_eq_mul_of_left_le_of_ne
      he hbase hprod hleft_le hne with
    ⟨_, _, _, _, p, hp, _, hp_new, hp_left⟩
  have hp_eq_one : p = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hp_new hp_left
  exact hp.not_dvd_one (by rw [hp_eq_one])

/-- A split ramification square with divisibility on both upper branches has a
common quotient.  This isolates the arithmetic datum still left after the
source square and branch divisibilities have been constructed. -/
theorem exists_commonQuotient_of_mul_eq_mul_of_dvd_of_dvd
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (hnew : 0 < newRamificationIndex)
    (hleftBaseChanged : 0 < leftBaseChangedIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hnew_dvd : newRamificationIndex ∣ e)
    (hleftBaseChanged_dvd :
      leftBaseChangedIndex ∣ baseChangeRamificationIndex) :
    ∃ commonQuotient,
      e = newRamificationIndex * commonQuotient ∧
        baseChangeRamificationIndex =
          leftBaseChangedIndex * commonQuotient := by
  rcases hnew_dvd with ⟨rightQuotient, hrightQuotient⟩
  rcases hleftBaseChanged_dvd with ⟨baseQuotient, hbaseQuotient⟩
  have hbaseQuotient_eq : baseQuotient = rightQuotient := by
    have hcancel_left :
        baseQuotient * newRamificationIndex =
          newRamificationIndex * rightQuotient := by
      apply Nat.eq_of_mul_eq_mul_left hleftBaseChanged
      calc
        leftBaseChangedIndex *
            (baseQuotient * newRamificationIndex) =
            (leftBaseChangedIndex * baseQuotient) *
              newRamificationIndex := by
          rw [mul_assoc]
        _ = baseChangeRamificationIndex *
              newRamificationIndex := by
          rw [← hbaseQuotient]
        _ = e * leftBaseChangedIndex := hprod
        _ =
            (newRamificationIndex * rightQuotient) *
              leftBaseChangedIndex := by
          rw [hrightQuotient]
        _ =
            leftBaseChangedIndex *
              (newRamificationIndex * rightQuotient) := by
          ac_rfl
    exact Nat.eq_of_mul_eq_mul_right hnew
      (by simpa [mul_comm] using hcancel_left)
  refine ⟨rightQuotient, hrightQuotient, ?_⟩
  rw [hbaseQuotient, hbaseQuotient_eq]

/-- Quotient form of
`exists_commonQuotient_of_mul_eq_mul_of_dvd_of_dvd`: after cancelling the two
upper branch indices, the two lower ramification indices leave the same
quotient. -/
theorem quotient_eq_of_mul_eq_mul_of_dvd_of_dvd
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (hnew : 0 < newRamificationIndex)
    (hleftBaseChanged : 0 < leftBaseChangedIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hnew_dvd : newRamificationIndex ∣ e)
    (hleftBaseChanged_dvd :
      leftBaseChangedIndex ∣ baseChangeRamificationIndex) :
    e / newRamificationIndex =
      baseChangeRamificationIndex / leftBaseChangedIndex := by
  rcases exists_commonQuotient_of_mul_eq_mul_of_dvd_of_dvd
      hnew hleftBaseChanged hprod hnew_dvd hleftBaseChanged_dvd with
    ⟨commonQuotient, heq, hbase⟩
  calc
    e / newRamificationIndex =
        (newRamificationIndex * commonQuotient) /
          newRamificationIndex := by
      rw [heq]
    _ = commonQuotient := by
      rw [Nat.mul_div_right _ hnew]
    _ =
        (leftBaseChangedIndex * commonQuotient) /
          leftBaseChangedIndex := by
      rw [Nat.mul_div_right _ hleftBaseChanged]
    _ = baseChangeRamificationIndex / leftBaseChangedIndex := by
      rw [hbase]

/-- Reconstruct the lower-index lcm from a split ramification square whose
upper branches divide their respective lower branches and are coprime. -/
theorem mul_eq_lcm_of_mul_eq_mul_of_dvd_of_dvd_of_coprime
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (hnew : 0 < newRamificationIndex)
    (hleftBaseChanged : 0 < leftBaseChangedIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hnew_dvd : newRamificationIndex ∣ e)
    (hleftBaseChanged_dvd :
      leftBaseChangedIndex ∣ baseChangeRamificationIndex)
    (hcop : Nat.Coprime newRamificationIndex leftBaseChangedIndex) :
    baseChangeRamificationIndex * newRamificationIndex =
      Nat.lcm e baseChangeRamificationIndex := by
  rcases hnew_dvd with ⟨rightQuotient, hrightQuotient⟩
  rcases hleftBaseChanged_dvd with ⟨baseQuotient, hbaseQuotient⟩
  subst e
  subst baseChangeRamificationIndex
  have hbaseQuotient_eq : baseQuotient = rightQuotient := by
    have hcancel_left :
        baseQuotient * newRamificationIndex =
          newRamificationIndex * rightQuotient := by
      apply Nat.eq_of_mul_eq_mul_left hleftBaseChanged
      calc
        leftBaseChangedIndex * (baseQuotient * newRamificationIndex) =
            (leftBaseChangedIndex * baseQuotient) *
              newRamificationIndex := by rw [mul_assoc]
        _ = (newRamificationIndex * rightQuotient) *
              leftBaseChangedIndex := hprod
        _ = leftBaseChangedIndex *
              (newRamificationIndex * rightQuotient) := by ac_rfl
    exact Nat.eq_of_mul_eq_mul_right hnew
      (by simpa [mul_comm] using hcancel_left)
  subst baseQuotient
  calc
    (leftBaseChangedIndex * rightQuotient) * newRamificationIndex =
        newRamificationIndex * leftBaseChangedIndex * rightQuotient := by
      ac_rfl
    _ = Nat.lcm (newRamificationIndex * rightQuotient)
          (leftBaseChangedIndex * rightQuotient) := by
      rw [Nat.lcm_mul_right, hcop.lcm_eq_mul]

/-- Split-product source form of the tame Abhyankar index bound. -/
theorem abhyankarIndexBound_of_mul_eq_mul_of_dvd_of_dvd_of_coprime
    {e baseChangeRamificationIndex newRamificationIndex
      leftBaseChangedIndex : ℕ}
    (hbase : 0 < baseChangeRamificationIndex)
    (hnew : 0 < newRamificationIndex)
    (hleftBaseChanged : 0 < leftBaseChangedIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        e * leftBaseChangedIndex)
    (hnew_dvd : newRamificationIndex ∣ e)
    (hleftBaseChanged_dvd :
      leftBaseChangedIndex ∣ baseChangeRamificationIndex)
    (hcop : Nat.Coprime newRamificationIndex leftBaseChangedIndex) :
    AbhyankarIndexBound e baseChangeRamificationIndex
      newRamificationIndex :=
  abhyankarIndexBound_of_mul_eq_lcm hbase
    (mul_eq_lcm_of_mul_eq_mul_of_dvd_of_dvd_of_coprime
      hnew hleftBaseChanged hprod hnew_dvd hleftBaseChanged_dvd hcop)

theorem eq_one_of_abhyankarIndexBound_of_dvd
    {e baseChangeRamificationIndex newRamificationIndex : ℕ}
    (he : 0 < e)
    (hbound :
      AbhyankarIndexBound e baseChangeRamificationIndex newRamificationIndex)
    (hdiv : e ∣ baseChangeRamificationIndex) :
    newRamificationIndex = 1 := by
  have hbound_one : newRamificationIndex ∣ 1 := by
    simpa [AbhyankarIndexBound, div_gcd_eq_one_of_dvd he hdiv] using hbound
  exact Nat.dvd_one.mp hbound_one

/-- If `newRamificationIndex` divides a ramification index which itself
divides a coprime base-change ramification index, then the new index is one. -/
theorem eq_one_of_dvd_of_dvd_of_coprime
    {e baseChangeRamificationIndex newRamificationIndex : ℕ}
    (hnew_dvd : newRamificationIndex ∣ e)
    (hdiv : e ∣ baseChangeRamificationIndex)
    (hcop : Nat.Coprime e baseChangeRamificationIndex) :
    newRamificationIndex = 1 :=
  Nat.eq_one_of_dvd_coprimes
    (hcop.coprime_dvd_left hnew_dvd) dvd_rfl
    (hnew_dvd.trans hdiv)

/-- Direct lcm-product absorption: if the base-change ramification index
absorbs the lower ramification index, then the new ramification index is one. -/
theorem eq_one_of_mul_eq_lcm_of_dvd
    {e baseChangeRamificationIndex newRamificationIndex : ℕ}
    (hbase : 0 < baseChangeRamificationIndex)
    (hprod :
      baseChangeRamificationIndex * newRamificationIndex =
        Nat.lcm e baseChangeRamificationIndex)
    (hdiv : e ∣ baseChangeRamificationIndex) :
    newRamificationIndex = 1 := by
  have he : 0 < e := by
    rcases hdiv with ⟨rightQuotient, hrightQuotient⟩
    rw [hrightQuotient] at hbase
    exact Nat.pos_of_mul_pos_left (by simpa [mul_comm] using hbase)
  exact eq_one_of_abhyankarIndexBound_of_dvd he
    (abhyankarIndexBound_of_mul_eq_lcm hbase hprod) hdiv

theorem abhyankarIndexBound_iff_dvd
    (e baseChangeRamificationIndex newRamificationIndex : ℕ) :
    AbhyankarIndexBound e baseChangeRamificationIndex newRamificationIndex ↔
      newRamificationIndex ∣ e / Nat.gcd e baseChangeRamificationIndex :=
  Iff.rfl

end TameAbhyankar

end
