/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.LocalizationLocalMap
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# The actual localized integral closure inside an extension field

Choose a prime above the base maximal ideal and realize its localization as
the image of the injective localization map into the extension field. This
subalgebra representation uses the canonical inclusion and scalar towers.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.FiniteExtensionLocalization

universe u v w

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- The actual integral closure of the base valuation ring in the extension field. -/
abbrev Normalization (base : DVF.{u, v} K) : Type w :=
  integralClosure base.valuationSubring L

private theorem normalization_faithful (base : DVF.{u, v} K) :
    FaithfulSMul base.valuationSubring (Normalization (L := L) base) := by
  apply (faithfulSMul_iff_algebraMap_injective
    base.valuationSubring (Normalization (L := L) base)).mpr
  intro x y hxy
  apply Subtype.ext
  apply (algebraMap K L).injective
  exact congrArg (fun z : Normalization (L := L) base => (z : L)) hxy

private theorem exists_prime (base : DVF.{u, v} K) :
    ∃ P : PrimeSpectrum (Normalization (L := L) base),
      P.asIdeal.IsMaximal ∧ P.asIdeal.LiesOver base.maximalIdeal := by
  have : FaithfulSMul base.valuationSubring (Normalization (L := L) base) :=
    normalization_faithful base
  obtain ⟨P, hP, hOver⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := Normalization (L := L) base) base.maximalIdeal
  exact ⟨⟨P, hP.isPrime⟩, hP, hOver⟩

/-- A chosen prime of the actual integral closure above the base maximal ideal. -/
def prime (base : DVF.{u, v} K) : PrimeSpectrum (Normalization (L := L) base) :=
  Classical.choose (exists_prime (L := L) base)

/-- The chosen prime is maximal. -/
theorem prime_isMaximal (base : DVF.{u, v} K) : (prime (L := L) base).asIdeal.IsMaximal :=
  (Classical.choose_spec (exists_prime (L := L) base)).1

/-- The chosen prime contracts to the base maximal ideal. -/
theorem prime_liesOver (base : DVF.{u, v} K) :
    (prime (L := L) base).asIdeal.LiesOver base.maximalIdeal :=
  (Classical.choose_spec (exists_prime (L := L) base)).2

/-- A prime above the nonzero maximal ideal of the base DVR is nonzero. -/
theorem prime_ne_bot (base : DVF.{u, v} K) : (prime (L := L) base).asIdeal ≠ ⊥ := by
  have : FaithfulSMul base.valuationSubring (Normalization (L := L) base) :=
    normalization_faithful base
  exact Ideal.ne_bot_of_mem_primesOver base.maximalIdeal_ne_bot
    ⟨(prime (L := L) base).isPrime, prime_liesOver base⟩

private theorem primeCompl_maps_to_units (base : DVF.{u, v} K)
    (y : (prime (L := L) base).asIdeal.primeCompl) :
    IsUnit (algebraMap (Normalization (L := L) base) L y) := by
  apply isUnit_iff_ne_zero.mpr
  apply (map_ne_zero_iff (algebraMap (Normalization (L := L) base) L)
    (IsIntegralClosure.algebraMap_injective
      (Normalization (L := L) base) base.valuationSubring L)).mpr
  exact nonZeroDivisors.ne_zero
    ((prime (L := L) base).asIdeal.primeCompl_le_nonZeroDivisors y.property)

private def localizationEmbedding (base : DVF.{u, v} K) :
    Localization.AtPrime (prime (L := L) base).asIdeal →ₐ[Normalization (L := L) base] L where
  toRingHom := IsLocalization.lift (primeCompl_maps_to_units (L := L) base)
  commutes' x := IsLocalization.lift_eq (primeCompl_maps_to_units (L := L) base) x

private theorem localizationEmbedding_injective (base : DVF.{u, v} K) :
    Function.Injective (localizationEmbedding (L := L) base) := by
  apply (IsLocalization.lift_injective_iff (primeCompl_maps_to_units (L := L) base)).mpr
  intro x y
  rw [(IsLocalization.injective (Localization.AtPrime (prime (L := L) base).asIdeal)
      (prime (L := L) base).asIdeal.primeCompl_le_nonZeroDivisors).eq_iff,
    (IsIntegralClosure.algebraMap_injective
      (Normalization (L := L) base) base.valuationSubring L).eq_iff]

/-- The localization as an actual subalgebra of the extension field. -/
def localizationSubalgebra (base : DVF.{u, v} K) : Subalgebra (Normalization (L := L) base) L :=
  (localizationEmbedding base).range

/-- The localization of the actual integral closure at the selected prime. -/
abbrev LocalizationRing (base : DVF.{u, v} K) : Type w :=
  localizationSubalgebra (L := L) base

/-- The actual subalgebra has the localization universal property. -/
theorem localization_isLocalization (base : DVF.{u, v} K) :
    IsLocalization.AtPrime (LocalizationRing (L := L) base) (prime (L := L) base).asIdeal :=
  IsLocalization.isLocalization_of_algEquiv (prime (L := L) base).asIdeal.primeCompl
    (AlgEquiv.ofInjective (localizationEmbedding base) (localizationEmbedding_injective base))

attribute [local instance] localization_isLocalization

/-- The localized integral closure has a local algebra map from the base valuation ring. -/
theorem baseMap_isLocalHom (base : DVF.{u, v} K) :
    IsLocalHom (algebraMap base.valuationSubring (LocalizationRing (L := L) base)) := by
  have : (prime (L := L) base).asIdeal.LiesOver base.maximalIdeal := prime_liesOver base
  exact localizationAtPrime_algebraMap_isLocalHom
    base.valuationSubring (LocalizationRing (L := L) base) (prime (L := L) base).asIdeal

end ValuationTheory.DiscreteValuationField.FiniteExtensionLocalization
