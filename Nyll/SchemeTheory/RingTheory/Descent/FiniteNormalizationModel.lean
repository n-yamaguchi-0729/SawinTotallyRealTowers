/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.FiniteSubalgebraLocalization
import Nyll.SchemeTheory.RingTheory.Descent.IntegralClosureLocalizationAway
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# A finite model of a normalization near one base prime

The model is a genuine subalgebra of the original algebra on `D(d)`. It
recovers that algebra after inverting `d`, and agrees with the integral
closure at the selected prime. Its generators come from the two actual
localizations, rather than from a finiteness assumption on the normalization.
-/

noncomputable section

namespace SchemeTheory

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Finite generation of the normalization at one prime and on `D(d)`
produces a finite model inside the original algebra, with both comparisons. -/
theorem exists_finite_normalization_model
    {R : Type u} [CommRing R] (d : R)
    (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away d A]
    (T : Type u) [CommRing T] [Algebra R T] [Algebra A T]
    [IsScalarTower R A T] [Module.Finite A T]
    (p : PrimeSpectrum R)
    [Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T)] :
    ∃ C : Subalgebra R T, Module.Finite R C ∧
      IsLocalization.Away (algebraMap R C d) T ∧
      Nonempty ((Localization.AtPrime p.asIdeal ⊗[R] C) ≃ₐ[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R T)) := by
  let B := integralClosure R T
  let P := Localization.AtPrime p.asIdeal
  let : IsLocalization.Away (algebraMap R B d) T :=
    integralClosure_isLocalization_away d A T
  let : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers d)) T :=
    inferInstance
  let : Algebra.IsPushout R A B T :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers d) A B T).symm
  let eBT : A ⊗[R] B ≃ₐ[A] T := Algebra.IsPushout.equiv R A B T
  let : Module.Finite A (A ⊗[R] B) :=
    Module.Finite.of_surjective eBT.symm.toLinearMap eBT.symm.surjective
  obtain ⟨D, hDfinite, hDp, hDd⟩ := exists_finite_subalgebra_two_localizations
    (B := B) p.asIdeal.primeCompl (Submonoid.powers d) P A
  let : Module.Finite R D := hDfinite
  let C : Subalgebra R T := D.map B.val
  let eDC : D ≃ₐ[R] C := D.equivMapOfInjective B.val Subtype.val_injective
  have hCfinite : Module.Finite R C :=
    Module.Finite.of_surjective eDC.toLinearMap eDC.surjective
  let ep : P ⊗[R] C ≃ₐ[P] P ⊗[R] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := P) (A₁ := P)) eDC.symm).trans
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lTensor (S := P) P D.val) hDp)
  let ed : A ⊗[R] C ≃ₐ[A] T :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := A) (A₁ := A)) eDC.symm).trans
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lTensor (S := A) A D.val) hDd)).trans eBT
  have hval (c : C) : ((eDC.symm c : D) : B).val = c.val := by
    have h := congrArg Subtype.val (eDC.apply_symm_apply c)
    exact h
  have hed : ed.toRingHom.comp (algebraMap C (A ⊗[R] C)) = algebraMap C T := by
    apply RingHom.ext
    intro c
    change ed ((1 : A) ⊗ₜ[R] c) = c.val
    change eBT ((1 : A) ⊗ₜ[R] ((eDC.symm c : D) : B)) = c.val
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    exact hval c
  let : Algebra.IsPushout R A C T := Algebra.IsPushout.of_equiv ed hed
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers d)) T :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers d) A).mpr
      (Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout R A C T))
  refine ⟨C, hCfinite, ?_, ⟨ep⟩⟩
  simpa only [Algebra.algebraMapSubmonoid, Submonoid.map_powers] using hloc

end SchemeTheory
