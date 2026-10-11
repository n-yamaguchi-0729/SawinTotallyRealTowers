/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.KummerAdjoinRoot
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.EisensteinResidue
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# A cyclic Kummer extension with unchanged residue field

A prime uniformizer supplies an Eisenstein Kummer polynomial. A primitive
root of unity makes its actual root extension cyclic Galois. The localized
integral closure then supplies the extension valuation, and the Eisenstein
power basis proves that the actual residue-field map is surjective.

The comparison uses only the canonical coefficient-ring algebra belonging
to that valuation tower. No residue characteristic or residue separability
condition is imposed.
-/

namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v

/-- A Henselian DVF containing a primitive `r`-th root of unity has a
cyclic degree-`r` extension with surjective actual residue-field map. -/
theorem HenselianDVF.exists_cyclic_kummer_extension_residueMap_surjective
    {K : Type u} [Field K] (base : HenselianDVF.{u, v} K)
    (r : ℕ) [Fact r.Prime] (ζ : K) (hζ : IsPrimitiveRoot ζ r) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (target : HenselianDVF.{u, 0} L)
      (_ : base.toDVF.valuation.HasExtension target.toDVF.valuation),
      Module.finrank K L = r ∧ IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧
      Function.Surjective (ValuedExtension.residueMap base.toDVF target.toDVF) := by
  let R : Type u := base.valuationSubring
  let : IsDiscreteValuationRing R := base.toDVF.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing R K := base.toDVF.valuationSubring_isFractionRing
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨L, _, _, scalarAlgebra, scalarTower, B, hdegree, hpower,
      hminpolyK, hminpolyRExisting, hGalois, hcyclic⟩ :=
    exists_cyclic_kummer_extension_of_prime_parameter R K π hπ.prime r ζ hζ
  clear hpower hminpolyRExisting scalarTower scalarAlgebra
  let : FiniteDimensional K L := B.finite
  let : IsGalois K L := hGalois
  let target : HenselianDVF.{u, 0} L :=
    FiniteExtensionLocalization.henselianDVF base
  let : base.toDVF.valuation.HasExtension target.toDVF.valuation :=
    FiniteExtensionLocalization.henselianDVF_hasExtension base
  let f : R[X] := X ^ r - C π
  have hfmap : f.map (algebraMap R K) = minpoly K B.gen := by
    rw [hminpolyK]
    simp only [f, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  have hrootK : aeval B.gen (f.map (algebraMap R K)) = 0 := by
    rw [hfmap]
    exact minpoly.aeval K B.gen
  have hrootR : aeval B.gen f = 0 :=
    (Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R K L).symm
      f B.gen).trans hrootK
  have hintegral : IsIntegral R B.gen :=
    ⟨f, monic_X_pow_sub_C π (Fact.out : r.Prime).ne_zero, hrootR⟩
  have hminpolyR : minpoly R B.gen = f := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hintegral]
    exact hfmap.symm
  have hEisenstein : (minpoly base.valuationSubring B.gen).IsEisensteinAt
      base.maximalIdeal := by
    change (minpoly R B.gen).IsEisensteinAt (IsLocalRing.maximalIdeal R)
    rw [hminpolyR, hπ.maximalIdeal_eq]
    exact X_pow_sub_C_isEisensteinAt_of_prime_parameter π hπ.prime r
      (Fact.out : r.Prime).pos
  have hresidue : Function.Surjective
      (ValuedExtension.residueMap base.toDVF target.toDVF) :=
    residueMap_surjective_of_minpoly_isEisensteinAt base target.toDVF B hEisenstein
  exact ⟨L, inferInstance, inferInstance, B.finite, target, inferInstance,
    hdegree, hGalois, hcyclic, hresidue⟩

end ValuationTheory.DiscreteValuationField
