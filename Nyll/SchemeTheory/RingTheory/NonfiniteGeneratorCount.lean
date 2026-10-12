/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Find
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# The nonfinite-generator invariant

Stacks Project, Section 58.32, defines `NF` by considering every ordered
finite algebra-generating family, taking its longest integral prefix, and
minimizing the number of remaining generators. This file constructs that
literal minimum and proves that it vanishes precisely for a finite algebra.

The algebra structure records the original map `φ`; integrality uses its
actual coefficient map. The auxiliary quotient map `τ` does not occur in
this numerical definition. The construction works for any finite-type
commutative algebra, hence for the original étale map, and allows the zero
ring and empty generating families. It does not assert the subsequent
positive-characteristic coordinate-modification lemma.

Source: https://stacks.math.columbia.edu/tag/0G1E
-/

noncomputable section

namespace SchemeTheory

universe u v

variable (R : Type u) {C : Type v} [CommRing R] [CommRing C] [Algebra R C]

/-- The largest length of an integral prefix in the displayed ordered family. -/
def integralPrefixLength {r : ℕ} (y : Fin r → C) : ℕ := by
  classical
  exact Nat.findGreatest (fun s : ℕ => ∀ i : Fin r, i.val < s → IsIntegral R (y i)) r

/-- The chosen prefix never exceeds the length of the family. -/
theorem integralPrefixLength_le {r : ℕ} (y : Fin r → C) :
    integralPrefixLength R y ≤ r := by
  classical
  exact Nat.findGreatest_le r

/-- Every element in the chosen prefix is integral over the original base. -/
theorem integralPrefixLength_spec {r : ℕ} (y : Fin r → C) :
    ∀ i : Fin r, i.val < integralPrefixLength R y → IsIntegral R (y i) := by
  classical
  exact Nat.findGreatest_spec
    (P := fun s : ℕ => ∀ i : Fin r, i.val < s → IsIntegral R (y i))
    (Nat.zero_le r)
    (show ∀ i : Fin r, i.val < 0 → IsIntegral R (y i) from
      fun i hi => False.elim (Nat.not_lt_zero i.val hi))

/-- Any integral prefix is no longer than the constructed largest prefix. -/
theorem le_integralPrefixLength {r : ℕ} (y : Fin r → C) {s : ℕ}
    (hs : s ≤ r) (hy : ∀ i : Fin r, i.val < s → IsIntegral R (y i)) :
    s ≤ integralPrefixLength R y := by
  classical
  exact Nat.le_findGreatest hs hy

/-- The prefix has full length exactly when all displayed generators are integral. -/
theorem integralPrefixLength_eq_iff {r : ℕ} (y : Fin r → C) :
    integralPrefixLength R y = r ↔ ∀ i : Fin r, IsIntegral R (y i) := by
  constructor
  · intro h i
    apply integralPrefixLength_spec R y i
    rw [h]
    exact i.isLt
  · intro hy
    exact Nat.le_antisymm (integralPrefixLength_le R y)
      (le_integralPrefixLength R y le_rfl (fun i _ => hy i))

variable (C)

private theorem exists_ordered_algebra_generators [Algebra.FiniteType R C] :
    ∃ (r : ℕ) (y : Fin r → C), Algebra.adjoin R (Set.range y) = ⊤ := by
  obtain ⟨r, f, hf⟩ :=
    (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).mp inferInstance
  refine ⟨r, f ∘ MvPolynomial.X, ?_⟩
  rw [Algebra.adjoin_range_eq_range_aeval, ← MvPolynomial.aeval_unique f]
  exact (AlgHom.range_eq_top f).mpr hf

private theorem exists_nonfinite_generator_count [Algebra.FiniteType R C] :
    ∃ d : ℕ, ∃ (r : ℕ) (y : Fin r → C),
      Algebra.adjoin R (Set.range y) = ⊤ ∧ r - integralPrefixLength R y = d := by
  obtain ⟨r, y, hy⟩ := exists_ordered_algebra_generators R C
  exact ⟨r - integralPrefixLength R y, r, y, hy, rfl⟩

/-- The invariant `NF` of Stacks 58.32: the minimum, over all ordered finite
algebra-generating families, of their length minus their longest integral prefix. -/
def nonfiniteGeneratorCount [Algebra.FiniteType R C] : ℕ := by
  classical
  exact Nat.find (exists_nonfinite_generator_count R C)

/-- The minimum is attained by an actual ordered algebra-generating family. -/
theorem nonfiniteGeneratorCount_spec [Algebra.FiniteType R C] :
    ∃ (r : ℕ) (y : Fin r → C), Algebra.adjoin R (Set.range y) = ⊤ ∧
      r - integralPrefixLength R y = nonfiniteGeneratorCount R C := by
  classical
  exact Nat.find_spec (exists_nonfinite_generator_count R C)

/-- Every displayed generating family bounds the minimum from above. -/
theorem nonfiniteGeneratorCount_le [Algebra.FiniteType R C]
    {r : ℕ} (y : Fin r → C) (hy : Algebra.adjoin R (Set.range y) = ⊤) :
    nonfiniteGeneratorCount R C ≤ r - integralPrefixLength R y := by
  classical
  exact Nat.find_min' (exists_nonfinite_generator_count R C) ⟨r, y, hy, rfl⟩

/-- A known integral prefix, even before computing the longest one, bounds `NF`.
This is the bound used after modifying the polynomial coordinates. -/
theorem nonfiniteGeneratorCount_le_of_prefix [Algebra.FiniteType R C]
    {r s : ℕ} (y : Fin r → C) (hy : Algebra.adjoin R (Set.range y) = ⊤)
    (hs : s ≤ r) (hint : ∀ i : Fin r, i.val < s → IsIntegral R (y i)) :
    nonfiniteGeneratorCount R C ≤ r - s :=
  (nonfiniteGeneratorCount_le R C y hy).trans
    (Nat.sub_le_sub_left (le_integralPrefixLength R y hs hint) r)

/-- The original normalization-failure invariant vanishes exactly when the
algebra is finite as a module over its base. No nonzero-ring hypothesis is needed. -/
theorem nonfiniteGeneratorCount_eq_zero_iff [Algebra.FiniteType R C] :
    nonfiniteGeneratorCount R C = 0 ↔ Module.Finite R C := by
  constructor
  · intro hzero
    obtain ⟨r, y, hy, hcount⟩ := nonfiniteGeneratorCount_spec R C
    rw [hzero] at hcount
    have hprefix : integralPrefixLength R y = r :=
      Nat.le_antisymm (integralPrefixLength_le R y) (Nat.sub_eq_zero_iff_le.mp hcount)
    have hint : ∀ i : Fin r, IsIntegral R (y i) :=
      (integralPrefixLength_eq_iff R y).mp hprefix
    have hfg : (Algebra.adjoin R (Set.range y)).toSubmodule.FG :=
      fg_adjoin_of_finite (Set.finite_range y) (by
        rintro x ⟨i, rfl⟩
        exact hint i)
    rw [hy] at hfg
    exact ⟨hfg⟩
  · intro hfinite
    have : Module.Finite R C := hfinite
    obtain ⟨r, y, hy⟩ := exists_ordered_algebra_generators R C
    have hprefix : integralPrefixLength R y = r :=
      (integralPrefixLength_eq_iff R y).mpr (fun i => IsIntegral.of_finite R (y i))
    have hbound := nonfiniteGeneratorCount_le R C y hy
    rw [hprefix, Nat.sub_self] at hbound
    exact Nat.eq_zero_of_le_zero hbound

end SchemeTheory
