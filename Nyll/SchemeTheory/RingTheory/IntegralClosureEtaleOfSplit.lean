/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.IntegralClosureSplitProduct
import Nyll.SchemeTheory.RingTheory.Descent.BoundaryNormalIntegralClosure
import Nyll.SchemeTheory.RingTheory.Descent.LocalizationNormalIntegralClosure
import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing


/-!
# Étale normalization after an actual generic splitting

A splitting over a pointed étale neighborhood gives a split product in a
localization by non-zero-divisors. Local normality of that étale neighborhood
shows it is integrally closed in that localization. Smooth base change of
integral closure and the explicit split-product normalization therefore make
the original integral closure étale after faithfully flat base change. Étale
descent gives the conclusion over the original normal domain.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace SchemeTheory

universe u v

/-- A splitting in a genuine localization by non-zero-divisors on a
faithfully flat étale neighborhood makes the original integral closure étale. -/
theorem integralClosure_etale_of_split_localization_after_faithfullyFlat_etale
    (R S B T : Type u) (ι : Type v)
    [CommRing R] [CommRing S] [CommRing B] [CommRing T]
    [IsDomain R] [IsIntegrallyClosed R]
    [Algebra R S] [Algebra R B] [Algebra S T]
    [Algebra.Etale R S] [Module.FaithfullyFlat R S] [Finite ι]
    (M : Submonoid S) (hM : M ≤ S⁰) [IsLocalization M T]
    (e : (S ⊗[R] B) ≃ₐ[S] (ι → T)) :
    Algebra.Etale R (integralClosure R B) := by
  have : IsIntegrallyClosedIn S T :=
    isIntegrallyClosedIn_localization_of_normal_boundary M hM T
      (fun q _ _ => Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
        R S q (Localization.AtPrime q))
  let eclosure : (S ⊗[R] integralClosure R B) ≃ₐ[S]
      integralClosure S (S ⊗[R] B) :=
    AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R S B)
      TensorProduct.toIntegralClosure_bijective_of_smooth
  let esplit : (S ⊗[R] integralClosure R B) ≃ₐ[S] (ι → S) :=
    eclosure.trans (e.mapIntegralClosure.trans (integralClosureSplitProductEquiv S T ι))
  have : Algebra.Etale S (S ⊗[R] integralClosure R B) :=
    Algebra.Etale.of_equiv esplit.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat S

/-- A generic splitting on a faithfully flat étale neighborhood forces the
actual integral closure to be étale over the original normal domain. -/
theorem integralClosure_etale_of_split_after_faithfullyFlat_etale
    (R S B T : Type u) (ι : Type v)
    [CommRing R] [CommRing S] [CommRing B] [CommRing T]
    [IsDomain R] [IsIntegrallyClosed R]
    [Algebra R S] [Algebra R B] [Algebra S T]
    [Algebra.Etale R S] [Module.FaithfullyFlat R S] [Finite ι]
    (d : R) (hd : d ≠ 0) [IsLocalization.Away (algebraMap R S d) T]
    (e : (S ⊗[R] B) ≃ₐ[S] (ι → T)) :
    Algebra.Etale R (integralClosure R B) := by
  have hleft : IsLeftRegular (algebraMap R S d) := by
    change Function.Injective (fun x : S => algebraMap R S d * x)
    simpa only [IsSMulRegular, Algebra.smul_def] using
      (Module.Flat.isSMulRegular_of_isRegular (M := S) (IsRegular.of_ne_zero hd))
  have hdS : algebraMap R S d ∈ S⁰ := by
    have hr : IsRegular (algebraMap R S d) :=
      ⟨hleft, fun x y h => hleft ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩
    exact hr.mem_nonZeroDivisors
  exact integralClosure_etale_of_split_localization_after_faithfullyFlat_etale
    R S B T ι (Submonoid.powers (algebraMap R S d)) (Submonoid.powers_le.mpr hdS) e

/-- The actual generic-fiber splitting on a faithfully flat étale neighborhood
implies étaleness of normalization over an arbitrary integrally closed domain.
The generic tensor is its canonical localization; flatness supplies regular
images of every original denominator. -/
theorem integralClosure_etale_of_generic_split_after_faithfullyFlat_etale
    (R S B : Type u) (ι : Type v)
    [CommRing R] [CommRing S] [CommRing B] [IsDomain R] [IsIntegrallyClosed R]
    [Algebra R S] [Algebra R B]
    [Algebra.Etale R S] [Module.FaithfullyFlat R S] [Finite ι]
    (e : (S ⊗[R] B) ≃ₐ[S] (ι → (S ⊗[R] FractionRing R))) :
    Algebra.Etale R (integralClosure R B) := by
  have hM : Algebra.algebraMapSubmonoid S R⁰ ≤ S⁰ := by
    rintro s ⟨r, hr, rfl⟩
    have hleft : IsLeftRegular (algebraMap R S r) := by
      change Function.Injective (fun x : S => algebraMap R S r * x)
      simpa only [IsSMulRegular, Algebra.smul_def] using
        (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) hr)
    have hregular : IsRegular (algebraMap R S r) :=
      ⟨hleft, fun x y h => hleft ((mul_comm _ _).trans (h.trans (mul_comm _ _)))⟩
    exact hregular.mem_nonZeroDivisors
  exact integralClosure_etale_of_split_localization_after_faithfullyFlat_etale
    R S B (S ⊗[R] FractionRing R) ι (Algebra.algebraMapSubmonoid S R⁰) hM e

end SchemeTheory
