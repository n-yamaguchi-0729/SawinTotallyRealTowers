/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Algebraic.Integral
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.RingExtension

/-!
# Fraction fields along a finite local extension

Let `D / S` be a finite extension of domains, and let `q` lie over `p`.
This file fixes all canonical algebra structures between the two prime
localizations and the fraction field of `D`.  It also transports finite
dimensionality to the literal fraction field of `Sₚ`.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uS uD

variable {S : Type uS} {D : Type uD}
variable [CommRing S] [IsDomain S]
variable [CommRing D] [IsDomain D]
variable [Algebra S D] [FaithfulSMul S D] [Module.Finite S D]

/-- The canonical algebra from `Sₚ` to `D_q` when `q` lies over `p`. -/
noncomputable abbrev finiteLiesOverLocalizationAlgebra
    (p : Ideal S) (q : Ideal D) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
  Localization.AtPrime.algebraOfLiesOver p q

/-- The canonical embedding of `D_q` into the literal fraction field of
`D`. -/
noncomputable abbrev finiteLiesOverLocalizationToFractionRingAlgebra
    (q : Ideal D) [q.IsPrime] :
    Algebra (Localization.AtPrime q) (FractionRing D) :=
  localizationAtPrimeToFractionFieldAlgebra (K := FractionRing D) q

/-- The standard extension of fraction fields induced by `S → D`. -/
noncomputable abbrev finiteExtensionFractionRingAlgebra :
    Algebra (FractionRing S) (FractionRing D) :=
  FractionRing.liftAlgebra S (FractionRing D)

/-- The map `Sₚ → Frac(D)` factored through `Frac(S)`. -/
noncomputable abbrev finiteExtensionAtPrimeToFractionRingAlgebra
    (p : Ideal S) [p.IsPrime] :
    Algebra (Localization.AtPrime p) (FractionRing D) := by
  letI : Algebra (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
  letI : Algebra (FractionRing S) (FractionRing D) :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  exact ((algebraMap (FractionRing S) (FractionRing D)).comp
    (algebraMap (Localization.AtPrime p) (FractionRing S))).toAlgebra

/-- The literal fraction field of `Sₚ` acts on `Frac(D)` through the
canonical identification `Frac(Sₚ) ≃ Frac(S)`. -/
noncomputable abbrev finiteExtensionAtPrimeFractionRingAlgebra
    (p : Ideal S) [p.IsPrime] :
    Algebra (FractionRing (Localization.AtPrime p)) (FractionRing D) := by
  letI : Algebra (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
  letI : Algebra (FractionRing S) (FractionRing D) :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  exact fractionRingToExtensionAlgebra
    (V := Localization.AtPrime p) (K := FractionRing S)
      (L := FractionRing D)

omit [Module.Finite S D] in
/-- The maps `Sₚ → Frac(S) → Frac(D)` form the defining scalar tower. -/
theorem finiteExtensionAtPrime_fractionRingTower
    (p : Ideal S) [p.IsPrime] :
    letI : Algebra (Localization.AtPrime p) (FractionRing S) :=
      localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
    letI : Algebra (FractionRing S) (FractionRing D) :=
      finiteExtensionFractionRingAlgebra (S := S) (D := D)
    letI : Algebra (Localization.AtPrime p) (FractionRing D) :=
      finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) p
    IsScalarTower (Localization.AtPrime p) (FractionRing S)
      (FractionRing D) := by
  let : Algebra (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
  let : Algebra (FractionRing S) (FractionRing D) :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  let : Algebra (Localization.AtPrime p) (FractionRing D) :=
    finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) p
  exact IsScalarTower.of_algebraMap_eq' rfl

omit [Module.Finite S D] in
/-- The direct map from `Sₚ` to `Frac(D)` extends through the literal
fraction field of `Sₚ`. -/
theorem finiteExtensionAtPrime_literalFractionRingTower
    (p : Ideal S) [p.IsPrime] :
    letI : Algebra (Localization.AtPrime p) (FractionRing D) :=
      finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) p
    letI : Algebra (FractionRing (Localization.AtPrime p))
        (FractionRing D) :=
      finiteExtensionAtPrimeFractionRingAlgebra (S := S) (D := D) p
    IsScalarTower (Localization.AtPrime p)
      (FractionRing (Localization.AtPrime p)) (FractionRing D) := by
  let : Algebra (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
  let : Algebra (FractionRing S) (FractionRing D) :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  let : Algebra (Localization.AtPrime p) (FractionRing D) :=
    finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) p
  let : Algebra (FractionRing (Localization.AtPrime p))
      (FractionRing D) :=
    finiteExtensionAtPrimeFractionRingAlgebra (S := S) (D := D) p
  let : IsScalarTower (Localization.AtPrime p) (FractionRing S)
      (FractionRing D) :=
    finiteExtensionAtPrime_fractionRingTower (S := S) (D := D) p
  exact fractionRingToExtension_isScalarTower
    (V := Localization.AtPrime p) (K := FractionRing S)
      (L := FractionRing D)

/-- `Frac(D)` is finite over the literal fraction field of `Sₚ`. -/
theorem finiteExtensionAtPrime_fractionRing_finiteDimensional
    (p : Ideal S) [p.IsPrime] :
    letI : Algebra (FractionRing (Localization.AtPrime p))
        (FractionRing D) :=
      finiteExtensionAtPrimeFractionRingAlgebra (S := S) (D := D) p
    FiniteDimensional (FractionRing (Localization.AtPrime p))
      (FractionRing D) := by
  let : Algebra (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
  let : Algebra (FractionRing S) (FractionRing D) :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  let : SMul (FractionRing S) (FractionRing D) :=
    (finiteExtensionFractionRingAlgebra (S := S) (D := D)).toSMul
  let : Module (FractionRing S) (FractionRing D) :=
    (finiteExtensionFractionRingAlgebra (S := S) (D := D)).toModule
  let : FiniteDimensional (FractionRing S) (FractionRing D) := by
    infer_instance
  exact fractionRingToExtension_finiteDimensional
    (V := Localization.AtPrime p) (K := FractionRing S)
      (L := FractionRing D)

omit [Module.Finite S D] in
/-- The two canonical routes `Sₚ → D_q → Frac(D)` and
`Sₚ → Frac(S) → Frac(D)` agree. -/
theorem finiteLiesOverLocalization_fractionRingTower
    (p : Ideal S) (q : Ideal D) [p.IsPrime] [q.IsPrime] [q.LiesOver p] :
    letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      finiteLiesOverLocalizationAlgebra p q
    letI : Algebra (Localization.AtPrime q) (FractionRing D) :=
      finiteLiesOverLocalizationToFractionRingAlgebra q
    letI : Algebra (Localization.AtPrime p) (FractionRing D) :=
      finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) p
    IsScalarTower (Localization.AtPrime p) (Localization.AtPrime q)
      (FractionRing D) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    finiteLiesOverLocalizationAlgebra p q
  let : Algebra (Localization.AtPrime q) (FractionRing D) :=
    finiteLiesOverLocalizationToFractionRingAlgebra q
  let : Algebra (Localization.AtPrime p) (FractionRing D) :=
    finiteExtensionAtPrimeToFractionRingAlgebra (S := S) (D := D) p
  let : Algebra (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionFieldAlgebra (K := FractionRing S) p
  let : Algebra (FractionRing S) (FractionRing D) :=
    finiteExtensionFractionRingAlgebra (S := S) (D := D)
  let : IsScalarTower S (Localization.AtPrime p)
      (Localization.AtPrime q) := inferInstance
  let : IsScalarTower D (Localization.AtPrime q) (FractionRing D) :=
    localizationAtPrimeToFractionField_isScalarTower
      (K := FractionRing D) q
  let : IsScalarTower S (Localization.AtPrime p) (FractionRing S) :=
    localizationAtPrimeToFractionField_isScalarTower
      (K := FractionRing S) p
  let : IsScalarTower S (FractionRing S) (FractionRing D) :=
    FractionRing.isScalarTower_liftAlgebra S (FractionRing D)
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext p.primeCompl
  ext x
  simp only [RingHom.comp_apply]
  change algebraMap (FractionRing S) (FractionRing D)
      (algebraMap (Localization.AtPrime p) (FractionRing S)
        (algebraMap S (Localization.AtPrime p) x)) =
    algebraMap (Localization.AtPrime q) (FractionRing D)
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
        (algebraMap S (Localization.AtPrime p) x))
  calc
    algebraMap (FractionRing S) (FractionRing D)
        (algebraMap (Localization.AtPrime p) (FractionRing S)
          (algebraMap S (Localization.AtPrime p) x)) =
        algebraMap (FractionRing S) (FractionRing D)
          (algebraMap S (FractionRing S) x) := by
      rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime p)
        (FractionRing S)]
    _ = algebraMap S (FractionRing D) x :=
      (IsScalarTower.algebraMap_apply S (FractionRing S)
        (FractionRing D) x).symm
    _ = algebraMap D (FractionRing D) (algebraMap S D x) :=
      IsScalarTower.algebraMap_apply S D (FractionRing D) x
    _ = algebraMap (Localization.AtPrime q) (FractionRing D)
        (algebraMap D (Localization.AtPrime q) (algebraMap S D x)) :=
      IsScalarTower.algebraMap_apply D (Localization.AtPrime q)
        (FractionRing D) (algebraMap S D x)
    _ = algebraMap (Localization.AtPrime q) (FractionRing D)
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
          (algebraMap S (Localization.AtPrime p) x)) := by
      congr 1
      calc
        algebraMap D (Localization.AtPrime q) (algebraMap S D x) =
            algebraMap S (Localization.AtPrime q) x :=
          (IsScalarTower.algebraMap_apply S D
            (Localization.AtPrime q) x).symm
        _ = algebraMap (Localization.AtPrime p) (Localization.AtPrime q)
            (algebraMap S (Localization.AtPrime p) x) :=
          IsScalarTower.algebraMap_apply S (Localization.AtPrime p)
            (Localization.AtPrime q) x

end EtaleFundamentalGroups
