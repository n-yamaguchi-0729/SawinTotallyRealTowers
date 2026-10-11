/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Algebra.Ring.GeomSum

/-!
# Prime-to-residue torsion in the actual principal-unit group

For a principal unit x, reduction of the geometric sum of its first n
powers is n. If n is nonzero in the residue field, this sum is nonzero.
The geometric-sum identity then makes x^n = 1 imply x = 1. No Henselianity,
discreteness, completeness, or characteristic assumption on the field is used.
-/

namespace ValuationSubring

open scoped BigOperators

universe u

variable {K : Type u} [Field K]

/-- A principal unit killed by an integer nonzero in the residue field is one. -/
theorem principalUnit_eq_one_of_pow_eq_one_of_residue_natCast_ne_zero
    (A : ValuationSubring K) (x : A.principalUnitGroup)
    (n : ℕ) (hn : (n : IsLocalRing.ResidueField A) ≠ 0)
    (hx : x ^ n = 1) : x = 1 := by
  classical
  let g : A.principalUnitGroup →* Aˣ :=
    (Units.map (IsLocalRing.residue A).toMonoidHom).ker.subtype.comp
      A.principalUnitGroupEquiv.toMonoidHom
  let a : A := (g x : A)
  have hred : IsLocalRing.residue A a = 1 :=
    congrArg (fun z : (IsLocalRing.ResidueField A)ˣ =>
      (z : IsLocalRing.ResidueField A)) (A.principalUnitGroupEquiv x).property
  have hpow : a ^ n = 1 := by
    have hgpow : (g x) ^ n = 1 := by rw [← map_pow, hx, map_one]
    exact congrArg (fun z : Aˣ => (z : A)) hgpow
  let S : A := ∑ i ∈ Finset.range n, a ^ i
  have hSred : IsLocalRing.residue A S = (n : IsLocalRing.ResidueField A) := by
    change IsLocalRing.residue A (∑ i ∈ Finset.range n, a ^ i) = _
    rw [map_sum]
    calc
      ∑ i ∈ Finset.range n, IsLocalRing.residue A (a ^ i) =
          ∑ i ∈ Finset.range n, (1 : IsLocalRing.ResidueField A) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [map_pow, hred, one_pow]
      _ = (n : IsLocalRing.ResidueField A) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hSne : S ≠ 0 := by
    intro hS
    apply hn
    rw [hS, map_zero] at hSred
    exact hSred.symm
  have hprod : S * (a - 1) = 0 := by
    change (∑ i ∈ Finset.range n, a ^ i) * (a - 1) = 0
    rw [geom_sum_mul, hpow, sub_self]
  have ha : a = 1 := sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left hSne)
  apply A.principalUnitGroupEquiv.injective
  rw [map_one]
  apply Subtype.ext
  apply Units.ext
  exact ha

end ValuationSubring
