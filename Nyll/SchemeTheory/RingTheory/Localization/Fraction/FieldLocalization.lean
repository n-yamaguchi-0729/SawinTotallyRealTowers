/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.LocalizationLocalization


/-!
# A prime localization inside a chosen fraction field

This file fixes the canonical algebra maps from a prime localization into an
arbitrary chosen fraction field and then into a field extension.  The latter
map is defined by composition through the fraction field, so the two scalar
towers are definitionally compatible and the localization lift is constructed
only once.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

/-- An algebraic extension of the displayed fraction field is the fraction
field of the actual integral closure. This is the existing normalization
supplier, now shared without changing its proof. -/
theorem integralClosure_isFractionRing_of_fractionField_algebraic
    (A : Type uA) (K : Type uK) (L : Type uL)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [Algebra.IsAlgebraic K L] :
    IsFractionRing (integralClosure A L) L := by
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  exact integralClosure.isFractionRing_of_algebraic
    (A := A) (L := L) (fun a ha => hinj (ha.trans (map_zero (algebraMap A L)).symm))

variable {A : Type uA} {K : Type uK}
variable [CommRing A] [IsDomain A]
variable [Field K] [Algebra A K] [IsFractionRing A K]

/-- The canonical map from the localization of `A` at `P` to a chosen
fraction field of `A`. -/
noncomputable abbrev localizationAtPrimeToFractionFieldAlgebra
    (P : Ideal A) [P.IsPrime] :
    Algebra (Localization.AtPrime P) K :=
  (IsLocalization.lift
    (M := P.primeCompl)
    (S := Localization.AtPrime P)
    (g := algebraMap A K)
    (fun y ↦ by
      rw [isUnit_iff_ne_zero,
        map_ne_zero_iff _ (IsFractionRing.injective A K)]
      exact fun hy ↦ y.2 (hy ▸ P.zero_mem))).toAlgebra

omit [IsDomain A] in
/-- The fraction-field map from a prime localization extends the original
map from `A`. -/
theorem localizationAtPrimeToFractionField_isScalarTower
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    IsScalarTower A (Localization.AtPrime P) K := by
  let := localizationAtPrimeToFractionFieldAlgebra (K := K) P
  exact IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm

/-- A chosen fraction field of `A` is also a fraction field of every prime
localization of `A`, for the canonical map above. -/
theorem localizationAtPrimeToFractionField_isFractionRing
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    IsFractionRing (Localization.AtPrime P) K := by
  let := localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsScalarTower A (Localization.AtPrime P) K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) P
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    P.primeCompl (Localization.AtPrime P) K

variable {L : Type uL} [Field L] [Algebra K L]

/-- The map from the localization of `A` at `P` to `L`, factored canonically
through the chosen fraction field `K`. -/
noncomputable abbrev localizationAtPrimeToExtensionAlgebra
    (P : Ideal A) [P.IsPrime] :
    Algebra (Localization.AtPrime P) L := by
  letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
  exact ((algebraMap K L).comp
    (algebraMap (Localization.AtPrime P) K)).toAlgebra

omit [IsDomain A] in
/-- The prime-localization, fraction-field, and extension maps form a scalar
tower by construction. -/
theorem localizationAtPrimeToFractionFieldToExtension_isScalarTower
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    IsScalarTower (Localization.AtPrime P) K L := by
  let := localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  exact IsScalarTower.of_algebraMap_eq' rfl

variable [Algebra A L] [IsScalarTower A K L]

omit [IsDomain A] in
/-- The canonical localization map is compatible with the original map
`A → L`. -/
theorem localizationAtPrimeToExtension_isScalarTower
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    IsScalarTower A (Localization.AtPrime P) L := by
  let := localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : IsScalarTower A (Localization.AtPrime P) K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) P
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  change algebraMap A L x =
    algebraMap K L
      (algebraMap (Localization.AtPrime P) K
        (algebraMap A (Localization.AtPrime P) x))
  rw [← IsScalarTower.algebraMap_apply A (Localization.AtPrime P) K,
    ← IsScalarTower.algebraMap_apply A K L]

end EtaleFundamentalGroups
