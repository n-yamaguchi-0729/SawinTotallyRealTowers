/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Normalization.Inertia
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-!
# Normalizations over an arbitrary discrete valuation ring

For a DVR the contraction of every maximal prime in a finite normalization is
the unique maximal ideal of the base.  Consequently, all residue fields in a
normalization tower have the same exponential characteristic as the fixed
residue field of the DVR.
-/

noncomputable section


universe uV uK uE

namespace TameAbhyankar.SGA1

attribute [local instance] Ideal.Quotient.field Module.Free.of_divisionRing

/-- A discrete valuation ring is a Dedekind domain.  This named helper is
useful when specializing results whose base is stated as an arbitrary
Dedekind domain. -/
theorem isDedekindDomain_of_isDiscreteValuationRing
    (V : Type uV) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    IsDedekindDomain V := by
  infer_instance

variable {V : Type uV} {K : Type uK} {E : Type uE}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [Field K] [Field E]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K E] [Algebra V E] [IsScalarTower V K E]
variable (M : IntermediateField K E)
variable [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]

section GaloisTower

variable [FiniteDimensional K E] [IsGalois K E] [IsGalois K M]

local instance dvrNormalizationDedekind : IsDedekindDomain V :=
  isDedekindDomain_of_isDiscreteValuationRing V

local instance dvrNormalizationAlgebra :
    Algebra (integralClosure V M) (integralClosure V E) :=
  normalizationAlgebra (V := V) (K := K) (E := E) M

local instance dvrNormalizationScalarTower :
    IsScalarTower V (integralClosure V M) (integralClosure V E) :=
  normalizationScalarTower (V := V) M

local instance dvrLowerPrime_liesOver
    (Q : Ideal (integralClosure V E)) :
    Q.LiesOver
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance dvrBasePrime_liesOver
    (Q : Ideal (integralClosure V E)) :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).LiesOver
      (normalizationBasePrime (V := V) (K := K) (E := E) M Q) where
  over := rfl

local instance dvrLowerPrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationLowerPrime_isMaximal (V := V) M Q

local instance dvrBasePrime_isMaximal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    (normalizationBasePrime (V := V) (K := K) (E := E) M Q).IsMaximal :=
  normalizationBasePrime_isMaximal (V := V) M Q

omit [Algebra V K] [IsFractionRing V K] [IsScalarTower V K E]
  [IsScalarTower V K M] [FiniteDimensional K E] [IsGalois K E]
  [IsGalois K M] in
/-- The base contraction of every maximal prime of the top normalization is
the unique maximal ideal of the DVR. -/
theorem normalizationBasePrime_eq_maximalIdeal
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    normalizationBasePrime (V := V) (K := K) (E := E) M Q =
      IsLocalRing.maximalIdeal V :=
  IsLocalRing.eq_maximalIdeal
    (dvrBasePrime_isMaximal (V := V) M Q)

omit [Algebra V K] [IsFractionRing V K] [IsScalarTower V K E]
  [IsScalarTower V K M] [FiniteDimensional K E] [IsGalois K E]
  [IsGalois K M] in
/-- The residue field of the contraction in the normalization in `M` has the
same exponential characteristic as the fixed residue field of the DVR. -/
theorem normalizationBase_ringExpChar_eq_lower
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    ringExpChar (V ⧸ IsLocalRing.maximalIdeal V) =
      ringExpChar
        (integralClosure V M ⧸
          normalizationLowerPrime (V := V) (K := K) (E := E) M Q) := by
  let :
      (normalizationLowerPrime (V := V) (K := K) (E := E) M Q).LiesOver
        (IsLocalRing.maximalIdeal V) := by
    rw [← normalizationBasePrime_eq_maximalIdeal (V := V) M Q]
    infer_instance
  simpa only [ringExpChar] using congrArg (fun n : ℕ => max n 1)
    (Algebra.ringChar_eq
      (V ⧸ IsLocalRing.maximalIdeal V)
      (integralClosure V M ⧸
        normalizationLowerPrime (V := V) (K := K) (E := E) M Q))

omit [Algebra V K] [IsFractionRing V K] [Algebra K E]
  [IsScalarTower V K E] [Algebra V M] [IsScalarTower V K M]
  [IsScalarTower V M E] [FiniteDimensional K E] [IsGalois K E]
  [IsGalois K M] in
/-- The residue field at a maximal prime of the top normalization has the
same exponential characteristic as the fixed residue field of the DVR. -/
theorem normalizationBase_ringExpChar_eq_top
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    ringExpChar (V ⧸ IsLocalRing.maximalIdeal V) =
      ringExpChar (integralClosure V E ⧸ Q) := by
  let : Algebra.IsIntegral V (integralClosure V E) :=
    IsIntegralClosure.isIntegral_algebra V E
  have hmax :
      (Q.comap (algebraMap V (integralClosure V E))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (algebraMap V (integralClosure V E)) (fun x ↦ Algebra.IsIntegral.isIntegral x) Q
  let : Q.LiesOver (IsLocalRing.maximalIdeal V) := by
    exact ⟨(IsLocalRing.eq_maximalIdeal hmax).symm⟩
  simpa only [ringExpChar] using congrArg (fun n : ℕ => max n 1)
    (Algebra.ringChar_eq
      (V ⧸ IsLocalRing.maximalIdeal V)
      (integralClosure V E ⧸ Q))

omit [Algebra V K] [IsFractionRing V K] [IsScalarTower V K E]
  [IsScalarTower V K M] [FiniteDimensional K E] [IsGalois K E]
  [IsGalois K M] in
/-- A fixed exponential residue characteristic of the DVR transports to the
lower and top residue fields for every maximal top prime `Q`. -/
theorem normalizationResidue_ringExpChar_eq_of_base
    (q : ℕ)
    (hchar : ringExpChar (V ⧸ IsLocalRing.maximalIdeal V) = q)
    (Q : Ideal (integralClosure V E)) [Q.IsMaximal] :
    ringExpChar
          (integralClosure V M ⧸
            normalizationLowerPrime (V := V) (K := K) (E := E) M Q) = q ∧
      ringExpChar (integralClosure V E ⧸ Q) = q := by
  exact ⟨(normalizationBase_ringExpChar_eq_lower (V := V) M Q).symm.trans hchar,
    (normalizationBase_ringExpChar_eq_top (V := V) Q).symm.trans hchar⟩

end GaloisTower

end TameAbhyankar.SGA1
