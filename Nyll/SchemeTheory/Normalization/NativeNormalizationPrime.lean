/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Prime contraction in subalgebra normalizations

Proves faithfulness and lies-over properties for subalgebra normalizations. For faithful
algebras over a discrete valuation ring, the contracted maximal prime is nonzero.
-/

namespace SchemeTheory

universe u v

/-- The actual normalization coefficient map remains faithful in every
native subalgebra of the original faithful algebra. -/
theorem subalgebraNormalizationCommAlgCat_faithfulSMul
    {A : Type u} {L : Type v} [CommRing A] [CommRing L]
    [Algebra A L] [FaithfulSMul A L] (S : Subalgebra A L) :
    FaithfulSMul A (subalgebraNormalizationCommAlgCat S) := by
  apply (faithfulSMul_iff_algebraMap_injective A _).mpr
  intro a b hab
  apply FaithfulSMul.algebraMap_injective A L
  exact congrArg (fun x : subalgebraNormalizationCommAlgCat S => x.val.val) hab

/-- A maximal prime of an actual normalization lies over the unique maximal
ideal of the local coefficient ring. -/
theorem normalizationCommAlgCat_liesOver_maximalIdeal
    {A : Type u} {L : Type v} [CommRing A] [IsLocalRing A]
    [CommRing L] [Algebra A L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal] :
    Q.LiesOver (IsLocalRing.maximalIdeal A) := by
  have : Algebra.IsIntegral A (normalizationCommAlgCat A L) :=
    inferInstanceAs (Algebra.IsIntegral A (integralClosure A L))
  have hmax : (Q.under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal Q
  exact ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩

/-- Literal contraction into a native finite normalization preserves the
original base prime. -/
theorem subalgebraNormalizationPrime_liesOver_maximalIdeal
    {A : Type u} {L : Type v} [CommRing A] [IsLocalRing A]
    [CommRing L] [Algebra A L] (S : Subalgebra A L)
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    (Q.comap (subalgebraNormalizationRingMap S)).LiesOver (IsLocalRing.maximalIdeal A) := by
  have := normalizationCommAlgCat_liesOver_maximalIdeal Q
  exact Ideal.LiesOver.of_eq_comap (p := IsLocalRing.maximalIdeal A) (Q := Q)
    (subalgebraNormalizationMap S) rfl

/-- The actual contracted prime is nonzero because its original DVR
coefficient maximal ideal is nonzero. -/
theorem subalgebraNormalizationPrime_ne_bot
    {A : Type u} {L : Type v} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing L] [Algebra A L] [FaithfulSMul A L] (S : Subalgebra A L)
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal] :
    Q.comap (subalgebraNormalizationRingMap S) ≠ ⊥ := by
  have := subalgebraNormalizationCommAlgCat_faithfulSMul S
  have := subalgebraNormalizationPrime_liesOver_maximalIdeal S Q
  exact Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) _

end SchemeTheory
