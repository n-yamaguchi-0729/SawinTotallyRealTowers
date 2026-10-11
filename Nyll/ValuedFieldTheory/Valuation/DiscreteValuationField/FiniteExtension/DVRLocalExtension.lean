/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Valuation extension from a local map into a discrete valuation ring

A local map of valuation rings with the given fraction-field map determines
an extension of valuations. Applied to an actual local DVR over the base
valuation ring, this supplies the extension property of its normalized valuation.
-/

namespace ValuationTheory.DiscreteValuationField

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A local map of valuation subrings over the field inclusion determines
the extension property, without completeness or discreteness assumptions. -/
theorem hasExtension_of_local_valuationSubring_map
    {ΓK ΓL : Type*} [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓL]
    (vK : _root_.Valuation K ΓK) (vL : _root_.Valuation L ΓL)
    (f : vK.valuationSubring →+* vL.valuationSubring) [IsLocalHom f]
    (hcoe : ∀ z : vK.valuationSubring,
      (f z : L) = algebraMap K L (z : K)) :
    vK.HasExtension vL := by
  apply _root_.Valuation.HasExtension.ofComapInteger
  ext z
  change algebraMap K L z ∈ vL.valuationSubring ↔ z ∈ vK.valuationSubring
  constructor
  · intro hz
    by_contra hn
    have hz0 : z ≠ 0 := fun heq => hn (heq ▸ vK.valuationSubring.zero_mem)
    have hinv : z⁻¹ ∈ vK.valuationSubring.nonunits :=
      vK.valuationSubring.inv_mem_nonunits_iff.mpr (Or.inr hn)
    let y : vK.valuationSubring :=
      ⟨z⁻¹, vK.valuationSubring.nonunits_subset hinv⟩
    have hy : y ∈ IsLocalRing.maximalIdeal vK.valuationSubring :=
      vK.valuationSubring.coe_mem_nonunits_iff.mp hinv
    have hfy : f y ∈ IsLocalRing.maximalIdeal vL.valuationSubring := map_nonunit f y hy
    let x : vL.valuationSubring := ⟨algebraMap K L z, hz⟩
    have hprod : f y * x = 1 := by
      apply Subtype.ext
      change (f y : L) * algebraMap K L z = 1
      rw [hcoe]
      change algebraMap K L (z⁻¹) * algebraMap K L z = 1
      rw [← map_mul, inv_mul_cancel₀ hz0, map_one]
    have hone : (1 : vL.valuationSubring) ∈ IsLocalRing.maximalIdeal vL.valuationSubring :=
      hprod ▸ (IsLocalRing.maximalIdeal vL.valuationSubring).mul_mem_right x hfy
    exact (IsLocalRing.maximalIdeal.isMaximal vL.valuationSubring).isPrime.one_notMem hone
  · intro hz
    have hmem := (f (⟨z, hz⟩ : vK.valuationSubring)).property
    rwa [hcoe] at hmem

/-- Evaluation of the DVR-to-valuation-subring equivalence is the fraction map. -/
theorem dvr_equivValuationSubring_coe
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L] (x : A) :
    (IsDiscreteValuationRing.equivValuationSubring (A := A) (K := L) x : L) =
      algebraMap A L x := by
  rfl

/-- A local DVR over the base valuation ring, with compatible fraction map,
supplies an actual extension of the base discrete valuation. -/
theorem hasExtension_dvr_valuation_of_isLocalHom (base : DVF K)
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A L] [IsFractionRing A L] [Algebra base.valuationSubring A]
    [IsScalarTower base.valuationSubring A L]
    [IsLocalHom (algebraMap base.valuationSubring A)] :
    base.valuation.HasExtension ((IsDiscreteValuationRing.maximalIdeal A).valuation L) := by
  let e := IsDiscreteValuationRing.equivValuationSubring (A := A) (K := L)
  let : IsLocalHom e.toRingHom := IsLocalHom.of_surjective e.toRingHom e.surjective
  let f : base.valuationSubring →+*
      ((IsDiscreteValuationRing.maximalIdeal A).valuation L).valuationSubring :=
    e.toRingHom.comp (algebraMap base.valuationSubring A)
  apply hasExtension_of_local_valuationSubring_map base.valuation
    ((IsDiscreteValuationRing.maximalIdeal A).valuation L) f
  intro z
  change (e (algebraMap base.valuationSubring A z) : L) = algebraMap K L (z : K)
  rw [dvr_equivValuationSubring_coe, ← IsScalarTower.algebraMap_apply base.valuationSubring A L]
  rfl

end ValuationTheory.DiscreteValuationField
