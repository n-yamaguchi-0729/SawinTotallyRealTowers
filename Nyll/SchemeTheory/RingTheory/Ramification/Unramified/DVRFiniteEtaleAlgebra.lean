/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.FiniteProduct
import Nyll.SchemeTheory.RingTheory.Ramification.Unramified.DVRNormalization
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Unramified normalization of a finite étale generic fibre

A finite étale algebra over a fraction field is a product of its actual
maximal-ideal quotient fields. The normalization in that algebra therefore
splits as the product of the normalizations in those fields. Over a DVR, the
ramification-index-one and separable-residue-extension conditions on every
field factor make the whole normalization finite étale.

Its generic fibre recovers the original algebra. This supplies the algebraic
extension at a codimension-one point used in
[Stacks Project, Tag 0H2W](https://stacks.math.columbia.edu/tag/0H2W).
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace SchemeTheory

attribute [local instance] Ideal.Quotient.field

/-- A finite étale algebra over a DVR's fraction field has finite étale
normalization when each of its actual field factors is unramified over the
DVR. The hypothesis consists of residue separability and ramification index
one at the maximal primes of each field factor's integral closure. -/
theorem finite_etale_integralClosure_of_finiteEtale_unramifiedOverDVR
    (R : Type u) (K : Type v) (A : Type w)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] [Algebra K A] [IsScalarTower R K A]
    [Module.Finite K A] [Algebra.Etale K A]
    (h : ∀ m : MaximalSpectrum A, IsUnramifiedOverDVR R (A ⧸ m.asIdeal)) :
    Module.Finite R (integralClosure R A) ∧
      Algebra.Etale R (integralClosure R A) := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  have hfactor (m : MaximalSpectrum A) :
      Module.Finite R (integralClosure R (A ⧸ m.asIdeal)) ∧
        Algebra.Etale R (integralClosure R (A ⧸ m.asIdeal)) :=
    finite_etale_integralClosure_of_unramifiedOverDVR R K (A ⧸ m.asIdeal) (h m)
  have : ∀ m : MaximalSpectrum A,
      Module.Finite R (integralClosure R (A ⧸ m.asIdeal)) :=
    fun m => (hfactor m).1
  have : ∀ m : MaximalSpectrum A,
      Algebra.Etale R (integralClosure R (A ⧸ m.asIdeal)) :=
    fun m => (hfactor m).2
  let e := integralClosureFactorsEquiv R A
  exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
    Algebra.Etale.of_equiv e.symm⟩

/-- The generic fibre of the literal normalization in a finite étale algebra
is the given algebra, including when that algebra has several field factors
or is the zero ring. No ramification hypothesis is needed for this comparison. -/
def integralClosureFiniteEtaleGenericFiberEquiv
    (R : Type u) (K : Type v) (A : Type w)
    [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [CommRing A] [Algebra R A] [Algebra K A] [IsScalarTower R K A]
    [Module.Finite K A] [Algebra.Etale K A] :
    K ⊗[R] integralClosure R A ≃ₐ[K] A := by
  classical
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  let : Fintype (MaximalSpectrum A) := Fintype.ofFinite (MaximalSpectrum A)
  let eNormalization : integralClosure R A ≃ₐ[R]
      ∀ m : MaximalSpectrum A, integralClosure R (A ⧸ m.asIdeal) :=
    integralClosureFactorsEquiv R A
  let eTensor : K ⊗[R] integralClosure R A ≃ₐ[K]
      K ⊗[R] (∀ m : MaximalSpectrum A, integralClosure R (A ⧸ m.asIdeal)) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eNormalization
  let eProduct : K ⊗[R]
      (∀ m : MaximalSpectrum A, integralClosure R (A ⧸ m.asIdeal)) ≃ₐ[K]
      ∀ m : MaximalSpectrum A, K ⊗[R] integralClosure R (A ⧸ m.asIdeal) :=
    Algebra.TensorProduct.piRight R K K
      (fun m : MaximalSpectrum A => integralClosure R (A ⧸ m.asIdeal))
  let eFields :
      (∀ m : MaximalSpectrum A, K ⊗[R] integralClosure R (A ⧸ m.asIdeal)) ≃ₐ[K]
      ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal :=
    AlgEquiv.piCongrRight fun m : MaximalSpectrum A =>
      integralClosureGenericFiberEquiv R K (A ⧸ m.asIdeal)
  exact eTensor.trans (eProduct.trans
    (eFields.trans ((IsArtinianRing.equivPi A).restrictScalars K).symm))

end SchemeTheory
