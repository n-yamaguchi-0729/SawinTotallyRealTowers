/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Valuation subrings in purely inseparable extensions

Let `E / F` be a purely inseparable extension of fields.  Membership in a
valuation subring of `E` can be tested after raising an element to a positive
power.  A sufficiently large exponential-characteristic power of every
element of `E` lies in the image of `F`.  It follows that a valuation subring
of `E` is determined by its restriction to `F`.

This supplies the inseparable part of valuation-extension counting: after
restricting from an algebraic extension to its maximal separable
subextension, no two valuation subrings become equal.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace PurelyInseparableValuation

universe u v

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/--
Membership in a valuation subring can be detected after taking any positive
power.

The reverse implication uses only the defining valuation-ring dichotomy.  If
`x⁻¹` belongs to the valuation subring as well as `x ^ n`, then
`x = x ^ n * (x⁻¹) ^ (n - 1)` belongs to it.
-/
theorem mem_iff_pow_mem
    (A : ValuationSubring E) (x : E) {n : ℕ} (hn : 0 < n) :
    x ∈ A ↔ x ^ n ∈ A := by
  constructor
  · intro hx
    exact A.toSubring.pow_mem hx n
  · intro hxpow
    rcases A.mem_or_inv_mem x with hx | hxinv
    · exact hx
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      have hxinvpow : (x⁻¹) ^ m ∈ A :=
        A.toSubring.pow_mem hxinv m
      have hproduct : x ^ (m + 1) * (x⁻¹) ^ m ∈ A :=
        A.mul_mem _ _ hxpow hxinvpow
      by_cases hxzero : x = 0
      · subst x
        exact A.zero_mem
      · have hidentity : x ^ (m + 1) * (x⁻¹) ^ m = x := by
          rw [pow_succ]
          calc
            x ^ m * x * (x⁻¹) ^ m =
                x * (x ^ m * (x⁻¹) ^ m) := by ac_rfl
            _ = x * (x * x⁻¹) ^ m := by rw [mul_pow]
            _ = x := by simp [hxzero]
        rwa [hidentity] at hproduct

/-- Restrict a valuation subring along the field-extension map. -/
def restriction (A : ValuationSubring E) : ValuationSubring F :=
  A.comap (algebraMap F E)

@[simp]
theorem mem_restriction (A : ValuationSubring E) (x : F) :
    x ∈ restriction A ↔ algebraMap F E x ∈ A :=
  Iff.rfl

/--
Restriction of valuation subrings along a purely inseparable field extension
is injective.

For `x : E`, choose `n` such that
`x ^ (ringExpChar F) ^ n = algebraMap F E y`.  Positive-power membership and
equality of the two restrictions then decide membership of `x`.
-/
theorem restriction_injective [IsPurelyInseparable F E] :
    Function.Injective
      (restriction : ValuationSubring E → ValuationSubring F) := by
  intro A B hrestriction
  apply ValuationSubring.ext
  intro x
  obtain ⟨n, y, hy⟩ :=
    IsPurelyInseparable.pow_mem F (ringExpChar F) x
  have hn : 0 < (ringExpChar F) ^ n :=
    expChar_pow_pos F (ringExpChar F) n
  rw [mem_iff_pow_mem A x hn, mem_iff_pow_mem B x hn, ← hy]
  change y ∈ restriction A ↔ y ∈ restriction B
  rw [hrestriction]

/-- Two valuation subrings over the same restriction are equal. -/
theorem eq_of_restriction_eq [IsPurelyInseparable F E]
    {A B : ValuationSubring E}
    (h : restriction (F := F) A = restriction (F := F) B) :
    A = B :=
  restriction_injective (F := F) (E := E) h

/--
Valuation subrings of `E` extending a fixed valuation subring of `F`.
-/
def Extensions (R : ValuationSubring F) :=
  {A : ValuationSubring E // restriction (F := F) A = R}

/--
A valuation subring has at most one extension through a purely inseparable
field extension.
-/
instance extensions_subsingleton [IsPurelyInseparable F E]
    (R : ValuationSubring F) :
    Subsingleton (Extensions (E := E) R) where
  allEq A B := by
    apply Subtype.ext
    apply restriction_injective (F := F) (E := E)
    exact A.property.trans B.property.symm

/--
Consequently, any finite collection of extensions of a fixed valuation
subring through a purely inseparable extension has cardinality at most one.
-/
theorem natCard_extensions_le_one [IsPurelyInseparable F E]
    (R : ValuationSubring F) [Finite (Extensions (E := E) R)] :
    Nat.card (Extensions (E := E) R) ≤ 1 :=
  Finite.card_le_one_iff_subsingleton.mpr inferInstance

/--
Restrict a valuation subring to the separable closure of `F` inside an
algebraic extension `E`.
-/
def restrictionToSeparableClosure [Algebra.IsAlgebraic F E]
    (A : ValuationSubring E) :
    ValuationSubring (separableClosure F E) :=
  A.comap (algebraMap (separableClosure F E) E)

/--
In an algebraic extension, valuation subrings inject into the valuation
subrings of the maximal separable subextension.

Indeed, `E` is purely inseparable over `separableClosure F E`, so the previous
restriction theorem applies verbatim.
-/
theorem restrictionToSeparableClosure_injective
    [Algebra.IsAlgebraic F E] :
    Function.Injective
      (restrictionToSeparableClosure (F := F) (E := E)) := by
  exact restriction_injective
    (F := separableClosure F E) (E := E)

/--
Restrict an extension of `R` to the maximal separable subextension.

The scalar-tower identity shows that the resulting valuation subring still
restricts to `R`.
-/
def extensionRestrictionToSeparableClosure [Algebra.IsAlgebraic F E]
    (R : ValuationSubring F) :
    Extensions (E := E) R →
      Extensions (F := F) (E := separableClosure F E) R :=
  fun A => by
    refine ⟨restrictionToSeparableClosure (F := F) A.1, ?_⟩
    unfold restriction restrictionToSeparableClosure
    rw [ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq F (separableClosure F E) E]
    exact A.property

/--
Extension counting over an algebraic field extension reduces injectively to
extension counting over its maximal separable subextension.
-/
theorem extensionRestrictionToSeparableClosure_injective
    [Algebra.IsAlgebraic F E] (R : ValuationSubring F) :
    Function.Injective
      (extensionRestrictionToSeparableClosure (E := E) R) := by
  intro A B h
  apply Subtype.ext
  apply restrictionToSeparableClosure_injective (F := F) (E := E)
  exact congrArg Subtype.val h

/--
The corresponding numerical extension count is bounded by the count over
the separable closure whenever that target collection is finite.
-/
theorem natCard_extensions_le_separableClosure
    [Algebra.IsAlgebraic F E] (R : ValuationSubring F)
    [Finite (Extensions (F := F) (E := separableClosure F E) R)] :
    Nat.card (Extensions (E := E) R) ≤
      Nat.card (Extensions (F := F) (E := separableClosure F E) R) :=
  Nat.card_le_card_of_injective
    (extensionRestrictionToSeparableClosure (E := E) R)
    (extensionRestrictionToSeparableClosure_injective (E := E) R)

end PurelyInseparableValuation
end Chapter06
end FieldArithmetic
