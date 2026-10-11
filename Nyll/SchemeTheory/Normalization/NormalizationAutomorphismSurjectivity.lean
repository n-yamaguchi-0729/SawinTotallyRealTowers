/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosureAutomorphismRestriction
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral

/-!
# Extending normalization automorphisms to fraction fields

Proves that every algebra automorphism of the integral closure in a finite field extension
extends to an automorphism over the base fraction field. Coefficient-square lemmas identify the
extension and its restriction.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- The actual native fraction extension commutes with its coefficient map. -/
theorem fractionRingEquiv_coefficient_square
    (B : Type u) (F : Type v) [CommRing B] [CommRing F]
    [Algebra B F] [IsFractionRing B F] (σ : B ≃+* B) :
    (IsFractionRing.ringEquivOfRingEquiv (K := F) (L := F) σ).toRingHom.comp
        (algebraMap B F) =
      (algebraMap B F).comp σ.toRingHom := by
  apply RingHom.ext
  intro b
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap σ b

/-- The actual normalization restriction is determined by its coefficient
square with the literal injective inclusion. -/
theorem mapIntegralClosure_eq_of_coefficient_square
    (A : Type u) (F : Type v) [CommRing A] [CommRing F] [Algebra A F]
    (σ : F ≃ₐ[A] F)
    (τ : integralClosure A F ≃ₐ[A] integralClosure A F)
    (hcoeff : σ.toRingHom.comp (integralClosure A F).toSubring.subtype =
      (integralClosure A F).toSubring.subtype.comp τ.toRingHom) :
    σ.mapIntegralClosure = τ := by
  apply AlgEquiv.ext
  intro b
  apply Subtype.ext
  exact RingHom.congr_fun hcoeff b

/-- Every intrinsic automorphism of the actual finite normalization is the
restriction of an actual automorphism of the finite field extension.
The fraction extension and its coefficient square are constructed natively. -/
theorem integralClosure_restrictScalars_surjective
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] :
    Function.Surjective
      (fun σ : F ≃ₐ[K] F => (σ.restrictScalars A).mapIntegralClosure) := by
  intro τ
  have : IsDomain A := (IsFractionRing.injective A K).isDomain
  have : IsFractionRing (integralClosure A F) F :=
    integralClosure.isFractionRing_of_finite_extension (A := A) K F
  let σ : F ≃ₐ[K] F := IsFractionRing.fieldEquivOfAlgEquiv K F F τ
  refine ⟨σ, ?_⟩
  apply mapIntegralClosure_eq_of_coefficient_square A F (σ.restrictScalars A) τ
  exact fractionRingEquiv_coefficient_square (integralClosure A F) F τ.toRingEquiv

end SchemeTheory
