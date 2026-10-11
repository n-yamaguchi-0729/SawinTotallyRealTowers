/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierAdjoinRoot
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.EisensteinResidue
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Henselian
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# A cyclic Artin--Schreier extension with unchanged residue field

Choose a prime uniformizer in the actual base valuation ring and construct
the Artin--Schreier extension from its reciprocal Eisenstein polynomial.
The localized integral closure supplies an actual extension valuation.
The constructed power basis and its integral minimal polynomial then give
surjectivity of the actual residue-field map.

The valuation, its extension property, the power basis, and the Eisenstein
condition are all outputs of the construction, never extra assumptions.
-/


namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v

/-- A characteristic-`p` Henselian DVF has a cyclic degree-`p` extension
with surjective actual residue-field map. -/
theorem HenselianDVF.exists_cyclic_prime_extension_residueMap_surjective
    {K : Type u} [Field K] (base : HenselianDVF.{u, v} K)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (target : HenselianDVF.{u, 0} L)
      (_ : base.toDVF.valuation.HasExtension target.toDVF.valuation),
      Module.finrank K L = p ∧ IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) ∧
      Function.Surjective (ValuedExtension.residueMap base.toDVF target.toDVF) := by
  let R : Type u := base.valuationSubring
  let : IsDiscreteValuationRing R := base.toDVF.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing R K := base.toDVF.valuationSubring_isFractionRing
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨L, _, _, B, _, hdegree, _, _, _, hminpolyK, hGalois, hcyclic⟩ :=
    exists_cyclic_artinSchreier_extension_of_prime_parameter R K π hπ.prime p
  let : FiniteDimensional K L := B.finite
  let : IsGalois K L := hGalois
  let target : HenselianDVF.{u, 0} L :=
    FiniteExtensionLocalization.henselianDVF base
  let : base.toDVF.valuation.HasExtension target.toDVF.valuation :=
    FiniteExtensionLocalization.henselianDVF_hasExtension base
  let f : R[X] := artinSchreierInversePolynomial π p
  have hmonic : f.Monic :=
    artinSchreierInversePolynomial_monic π p (Fact.out : p.Prime).one_lt
  have hrootK : aeval B.gen (f.map (algebraMap R K)) = 0 := by
    rw [← hminpolyK]
    exact minpoly.aeval K B.gen
  have hrootR : aeval B.gen f = 0 :=
    (Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R K L).symm
      f B.gen).trans hrootK
  have hintegral : IsIntegral R B.gen := ⟨f, hmonic, hrootR⟩
  have hminpolyR : minpoly R B.gen = f := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hintegral]
    exact hminpolyK
  have hEisenstein : (minpoly base.valuationSubring B.gen).IsEisensteinAt
      base.maximalIdeal := by
    change (minpoly R B.gen).IsEisensteinAt (IsLocalRing.maximalIdeal R)
    rw [hminpolyR, hπ.maximalIdeal_eq]
    exact artinSchreierInversePolynomial_isEisensteinAt π hπ.prime p
      (Fact.out : p.Prime).one_lt
  have hresidue : Function.Surjective
      (ValuedExtension.residueMap base.toDVF target.toDVF) :=
    residueMap_surjective_of_minpoly_isEisensteinAt base target.toDVF B hEisenstein
  exact ⟨L, inferInstance, inferInstance, B.finite, target, inferInstance,
    hdegree, hGalois, hcyclic, hresidue⟩

end ValuationTheory.DiscreteValuationField
