/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.BoundaryNormalIntegralClosure
import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalNormality
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Identifying a normalization on an etale neighborhood of a finite model

A finite model becomes etale after shrinking the base. Normality of the
original base along the boundary then makes the model's boundary local rings
normal. Integral closure across that boundary identifies the model with the
actual relative normalization, proving both finiteness and etaleness there.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct nonZeroDivisors

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An etale neighborhood of a finite model is an etale neighborhood of the
actual normalization, provided the base is normal along the boundary. -/
theorem finite_etale_integralClosure_on_model_neighborhood
    {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (C : Subalgebra R T) [Module.Finite R C]
    (d r : R) [IsLocalization.Away (algebraMap R C d) T]
    [Algebra.Etale R (Localization.Away (algebraMap R C r))]
    (hnormal : ∀ (p : Ideal R) [p.IsPrime], d ∈ p →
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    Module.Finite (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R T) ∧
      Algebra.Etale (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R T) := by
  let Rr := Localization.Away r
  let Cr := Localization.Away (algebraMap R C r)
  let Tr := Localization.Away (algebraMap R T r)
  let : Algebra Rr Cr := localizationAlgebra (Submonoid.powers r) C
  let : IsScalarTower R Rr Cr :=
    isScalarTower_localizationAlgebra (Submonoid.powers r) C
  let : Algebra Rr Tr := localizationAlgebra (Submonoid.powers r) T
  let : IsScalarTower R Rr Tr :=
    isScalarTower_localizationAlgebra (Submonoid.powers r) T
  let : IsLocalization.Away (algebraMap C T (algebraMap R C r)) Tr := by
    rw [← IsScalarTower.algebraMap_apply R C T]
    infer_instance
  let : Algebra Cr Tr :=
    localizationAlgebra (Submonoid.powers (algebraMap R C r)) T
  let : IsScalarTower C Cr Tr :=
    isScalarTower_localizationAlgebra (Rₘ := Cr) (Sₘ := Tr)
      (Submonoid.powers (algebraMap R C r)) T
  let : IsScalarTower Rr Cr Tr := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    apply RingHom.ext
    intro a
    change algebraMap Rr Tr (algebraMap R Rr a) =
      algebraMap Cr Tr (algebraMap Rr Cr (algebraMap R Rr a))
    rw [← IsScalarTower.algebraMap_apply R Rr Tr,
      ← IsScalarTower.algebraMap_apply R Rr Cr,
      IsScalarTower.algebraMap_apply R C Cr,
      ← IsScalarTower.algebraMap_apply C Cr Tr,
      ← IsScalarTower.algebraMap_apply R C Tr]
  let : IsLocalization.Away (algebraMap C Cr (algebraMap R C d)) Tr :=
    IsLocalization.Away.commutes Cr T Tr (algebraMap R C r) (algebraMap R C d)
  have hinj : Function.Injective (algebraMap Cr Tr) :=
    localizationAlgebra_injective Cr Tr Subtype.val_injective
  have hd : algebraMap C Cr (algebraMap R C d) ∈ Cr⁰ :=
    mem_nonZeroDivisors_of_injective hinj
      (IsLocalization.Away.algebraMap_isUnit (S := Tr)
        (algebraMap C Cr (algebraMap R C d))).mem_nonZeroDivisors
  let : IsIntegrallyClosedIn Cr Tr :=
    isIntegrallyClosedIn_away_of_normal_boundary
      (algebraMap C Cr (algebraMap R C d)) hd Tr (by
        intro q hq hdq
        have hdp : d ∈ q.under R := hdq
        let : IsDomain (Localization.AtPrime (q.under R)) := (hnormal _ hdp).1
        let : IsIntegrallyClosed (Localization.AtPrime (q.under R)) := (hnormal _ hdp).2
        exact isDomain_and_isIntegrallyClosed_atPrime_of_etale R Cr q)
  let : Module.Finite Rr Cr := Module.Finite.of_isLocalization R C (Submonoid.powers r)
  let : Algebra.IsIntegral Rr Cr := Algebra.IsIntegral.of_finite Rr Cr
  let : IsIntegralClosure Cr Rr Tr := IsIntegralClosure.of_isIntegrallyClosedIn
  let : Algebra.Etale R Rr := Algebra.Etale.of_isLocalizationAway r
  let : Algebra.Etale Rr Cr := Algebra.Etale.of_restrictScalars R Rr Cr
  let eC : Cr ≃ₐ[Rr] integralClosure Rr Tr :=
    IsIntegralClosure.equiv Rr Cr Tr (integralClosure Rr Tr)
  let : Algebra.IsPushout R Rr T Tr :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers r) Rr T Tr).symm
  let eT : Rr ⊗[R] T ≃ₐ[Rr] Tr := Algebra.IsPushout.equiv R Rr T Tr
  let eI : Rr ⊗[R] integralClosure R T ≃ₐ[Rr] integralClosure Rr Tr :=
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R Rr T)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization (Submonoid.powers r))).trans
        eT.mapIntegralClosure
  let e : Cr ≃ₐ[Rr] Rr ⊗[R] integralClosure R T := eC.trans eI.symm
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective, Algebra.Etale.of_equiv e⟩

end SchemeTheory
