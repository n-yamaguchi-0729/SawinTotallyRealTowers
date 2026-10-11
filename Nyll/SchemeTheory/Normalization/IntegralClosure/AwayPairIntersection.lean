/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.Polynomial.Tower
import Nyll.SchemeTheory.Normalization.IntegralClosure.PrimeAwayIntersection

/-!
# Integrality detected by two principal localizations

Suppose `x` is prime and does not divide the nonzero element `y` of an
integrally closed domain `A`.  For an algebraic extension of the fraction
field of `A`, integrality over both `A[1/x]` and `A[1/y]` implies integrality
over `A`.

The proof descends every coefficient of the minimal polynomial through the
intersection `A[1/x] ∩ A[1/y] = A`.  It uses no UFD structure on `A`.
-/

noncomputable section

namespace EtaleFundamentalGroups

open nonZeroDivisors

universe u v w

/-- Integrality over `A` is detected by the two principal localizations at a
prime `x` and at an element `y` not divisible by `x`. -/
theorem isIntegral_of_isIntegral_localizationAway_pair_of_prime
    {A : Type u} {K : Type v} {L : Type w}
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [Algebra.IsAlgebraic K L]
    {x y : A} (hx : Prime x) (hy : y ≠ 0) (hxy : ¬ x ∣ y)
    (z : L)
    (hzx :
      let Aₓ := Localization.subalgebra.ofField K (Submonoid.powers x)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
      IsIntegral Aₓ z)
    (hzy :
      let Aᵧ := Localization.subalgebra.ofField K (Submonoid.powers y)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hy))
      IsIntegral Aᵧ z) :
    IsIntegral A z := by
  have hcoeff : ∀ i : ℕ, (minpoly K z).coeff i ∈ (algebraMap A K).range := by
    intro i
    apply Algebra.mem_bot.mp
    apply mem_bot_of_mem_localizationAway_pair_of_prime
      hx hy hxy (z := (minpoly K z).coeff i)
    · let Aₓ := Localization.subalgebra.ofField K (Submonoid.powers x)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
      let : IsIntegrallyClosed Aₓ :=
        isIntegrallyClosed_of_isLocalization Aₓ (Submonoid.powers x)
          (Submonoid.powers_le.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mpr hx.ne_zero))
      have hmin := minpoly.isIntegrallyClosed_eq_field_fractions' K hzx
      rw [hmin, Polynomial.coeff_map]
      exact Subtype.prop _
    · let Aᵧ := Localization.subalgebra.ofField K (Submonoid.powers y)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hy))
      let : IsIntegrallyClosed Aᵧ :=
        isIntegrallyClosed_of_isLocalization Aᵧ (Submonoid.powers y)
          (Submonoid.powers_le.mpr
            (mem_nonZeroDivisors_iff_ne_zero.mpr hy))
      have hmin := minpoly.isIntegrallyClosed_eq_field_fractions' K hzy
      rw [hmin, Polynomial.coeff_map]
      exact Subtype.prop _
  obtain ⟨q, hq⟩ :=
    (Polynomial.mem_map_range (algebraMap A K)).mpr hcoeff
  change q.map (algebraMap A K) = minpoly K z at hq
  have hqmonic : q.Monic := by
    apply ((IsFractionRing.injective A K).monic_map_iff).mpr
    rw [hq]
    exact minpoly.monic (Algebra.IsIntegral.isIntegral z)
  refine ⟨q, hqmonic, ?_⟩
  have hzmin := minpoly.aeval K z
  rw [← hq] at hzmin
  change Polynomial.aeval z q = 0
  simpa only [Polynomial.aeval_map_algebraMap] using hzmin

end EtaleFundamentalGroups
