/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.LocalizationNormalIntegralClosure
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.Away.Basic


/-!
# Integral closure across a boundary with normal local rings

Only the local rings on the principal boundary need to be normal. An
integral element of the localization has no pole there: normality proves
local divisibility of its numerator, and divisibility descends from the
localizations at maximal ideals. No normality away from the boundary is
assumed.
-/

noncomputable section

namespace SchemeTheory

open scoped nonZeroDivisors

universe u v

/-- A ring with normal local rings on `V(d)` is integrally closed in its
localization away from the non-zero-divisor `d`. -/
theorem isIntegrallyClosedIn_away_of_normal_boundary
    {R : Type u} [CommRing R] (d : R) (hd : d ∈ R⁰)
    (T : Type v) [CommRing T] [Algebra R T] [IsLocalization.Away d T]
    (hnormal : ∀ (p : Ideal R) [p.IsMaximal], d ∈ p →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosedIn R T := by
  apply isIntegrallyClosedIn_localization_of_normal_boundary
    (Submonoid.powers d) (Submonoid.powers_le.mpr hd) T
  intro p hp hmeet
  obtain ⟨s, hs⟩ := hmeet
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : R) d).mp s.property
  have hdmem : d ∈ p :=
    (inferInstance : p.IsPrime).mem_of_pow_mem n (hn.symm ▸ hs)
  exact hnormal p hdmem

/-- A finite subalgebra which recovers `T` after inverting `d`, and is normal
on its boundary, is the actual relative integral closure. The inclusion in
`T` supplies the non-zero-divisor condition automatically. -/
theorem integralClosure_eq_finite_subalgebra_of_normal_boundary
    {R : Type u} {T : Type v} [CommRing R] [CommRing T] [Algebra R T]
    (C : Subalgebra R T) [Module.Finite R C]
    (d : C) [IsLocalization.Away d T]
    (hnormal : ∀ (p : Ideal C) [p.IsMaximal], d ∈ p →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    integralClosure R T = C := by
  have hd : d ∈ C⁰ := mem_nonZeroDivisors_of_injective
    (f := algebraMap C T) Subtype.val_injective
    (IsLocalization.Away.algebraMap_isUnit (S := T) d).mem_nonZeroDivisors
  let : IsIntegrallyClosedIn C T :=
    isIntegrallyClosedIn_away_of_normal_boundary d hd T hnormal
  apply le_antisymm
  · intro t ht
    have htC : IsIntegral C t := (show IsIntegral R t from ht).tower_top
    obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.algebraMap_eq_of_integral htC
    exact hc ▸ c.property
  · intro t ht
    exact (Algebra.IsIntegral.isIntegral (R := R) (⟨t, ht⟩ : C)).map C.val

end SchemeTheory
