/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.GroupRing
import Mathlib.Algebra.Ring.GeomSum

/-!
# Fox differential: right derivative — geometric series

The principal declarations in this module are:

- `geomSeries`
  The geometric series element is the finite sum of successive powers.
- `geomSeries_eq_sum_pow`
  The geometric series equals the finite sum of powers.
- `geomSeries_zero`
  The geometric series of length zero is zero.
- `geomSeries_one`
  The geometric series of length one is one.
-/

namespace FoxDifferential

/-- The geometric series element is the finite sum of successive powers. -/
noncomputable def geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    FoxDifferential.GroupRing A :=
  ∑ k ∈ Finset.range n, MonoidAlgebra.of ℤ A (a ^ k)

/-- The geometric series equals the finite sum of powers. -/
theorem geomSeries_eq_sum_pow {A : Type*} [Group A] (a : A) (n : ℕ) :
    geomSeries a n = ∑ k ∈ Finset.range n,
      (MonoidAlgebra.of ℤ A a : FoxDifferential.GroupRing A) ^ k := by
  simp only [geomSeries, map_pow, MonoidAlgebra.of_apply, MonoidAlgebra.single_pow, one_pow]

/-- The geometric series of length zero is zero. -/
@[simp]
theorem geomSeries_zero {A : Type*} [Group A] (a : A) :
    geomSeries a 0 = 0 := by
  simp only [geomSeries, Finset.range_zero, MonoidAlgebra.of_apply, Finset.sum_empty]

/-- The geometric series of length one is one. -/
@[simp]
theorem geomSeries_one {A : Type*} [Group A] (a : A) :
    geomSeries a 1 = 1 := by
  simpa [geomSeries] using (FoxDifferential.groupRing_of_one (H := A))

/-- The augmentation map has the stated value on group-ring elements. -/
@[simp]
theorem augmentation_geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    FoxDifferential.augmentation A (geomSeries a n) = n := by
  simp only [augmentation, augmentationAlgHom, AlgHom.toRingHom_eq_coe, geomSeries,
      MonoidAlgebra.of_apply,
  map_sum, RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.one_apply, Int.zsmul_eq_mul,
      mul_one,
  Finset.sum_const, Finset.card_range, Int.nsmul_eq_mul]

/-- The geometric series is nonzero when the natural length is nonzero. -/
theorem geomSeries_ne_zero_of_nat_ne_zero {A : Type*} [Group A]
    (a : A) {n : ℕ} (hn : n ≠ 0) :
    geomSeries a n ≠ 0 := by
  intro hzero
  have haug := congrArg (FoxDifferential.augmentation A) hzero
  rw [augmentation_geomSeries] at haug
  simp only [map_zero, Int.natCast_eq_zero] at haug
  exact hn haug

/-- The successor geometric series is obtained by adding the last power. -/
theorem geomSeries_succ_eq_add_pow {A : Type*} [Group A] (a : A) (n : ℕ) :
    geomSeries a (n + 1) =
      geomSeries a n + MonoidAlgebra.of ℤ A (a ^ n) := by
  simp only [geomSeries, Finset.range_add_one, MonoidAlgebra.of_apply, Finset.mem_range,
      lt_self_iff_false,
  not_false_eq_true, Finset.sum_insert, add_comm]

/--
The geometric series for a sum of lengths splits into the initial series plus the shifted tail
series.
-/
theorem geomSeries_add {A : Type*} [CommGroup A] (a : A) (m n : ℕ) :
    geomSeries a (m + n) =
      geomSeries a m + MonoidAlgebra.of ℤ A (a ^ m) * geomSeries a n := by
  induction n with
  | zero =>
      simp only [add_zero, MonoidAlgebra.of_apply, geomSeries_zero, mul_zero]
  | succ n ih =>
      rw [Nat.add_succ, geomSeries_succ_eq_add_pow, ih, geomSeries_succ_eq_add_pow]
      rw [mul_add]
      simp only [MonoidAlgebra.of_apply, pow_add, MonoidAlgebra.single_mul_single, mul_one]
      ring

/-- The successor geometric series satisfies the multiplicative recurrence. -/
theorem geomSeries_succ_eq_mul_add_one {A : Type*} [Group A] (a : A) (n : ℕ) :
    geomSeries a (n + 1) =
      geomSeries a n * MonoidAlgebra.of ℤ A a + 1 := by
  rw [geomSeries_eq_sum_pow, geomSeries_eq_sum_pow]
  let x : FoxDifferential.GroupRing A := MonoidAlgebra.of ℤ A a
  have h := geom_sum_succ (x := MulOpposite.op x) (n := n)
  have h2 := congrArg MulOpposite.unop h
  dsimp [x] at h2
  simpa using h2

/-- The difference \(1 - x^n\) factors as \((1 - x)\) times the geometric series. -/
theorem one_sub_pow_eq_one_sub_mul_geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    (1 - MonoidAlgebra.of ℤ A (a ^ n) : FoxDifferential.GroupRing A) =
      (1 - MonoidAlgebra.of ℤ A a) * geomSeries a n := by
  rw [geomSeries_eq_sum_pow]
  simpa [map_pow] using
    (mul_neg_geom_sum (MonoidAlgebra.of ℤ A a : FoxDifferential.GroupRing A) n).symm

/-- The difference \(x^n - 1\) factors as \((x - 1)\) times the geometric series. -/
theorem pow_sub_one_eq_sub_one_mul_geomSeries {A : Type*} [Group A] (a : A) (n : ℕ) :
    (MonoidAlgebra.of ℤ A (a ^ n) - 1 : FoxDifferential.GroupRing A) =
      (MonoidAlgebra.of ℤ A a - 1) * geomSeries a n := by
  rw [geomSeries_eq_sum_pow]
  simpa [map_pow] using
    (mul_geom_sum (MonoidAlgebra.of ℤ A a : FoxDifferential.GroupRing A) n).symm

end FoxDifferential
