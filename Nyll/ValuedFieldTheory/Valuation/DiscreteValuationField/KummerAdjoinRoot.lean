/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.KummerEisenstein
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.FieldTheory.KummerExtension
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.PowerBasis

/-!
# A cyclic Kummer extension from an Eisenstein parameter

The extension is the actual `AdjoinRoot (X ^ r - C π)` over the fraction
field. Eisenstein irreducibility supplies its field structure and power
basis; a primitive root of unity supplies the splitting field and Galois
property. Its integral minimal polynomial is identified before any
valuation is chosen, so the basis is ready for `EisensteinResidue`.
-/

namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v

/-- A prime parameter and a primitive `r`-th root of unity produce an
actual cyclic degree-`r` extension with the displayed integral minimal
polynomial. The coefficient-ring algebra and its tower are outputs of
the construction, alongside the fraction-field power basis. -/
theorem exists_cyclic_kummer_extension_of_prime_parameter
    (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Prime π) (r : ℕ) [Fact r.Prime]
    (ζ : K) (hζ : IsPrimitiveRoot ζ r) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L)
      (_ : Algebra R L) (_ : IsScalarTower R K L) (B : PowerBasis K L),
      Module.finrank K L = r ∧
      B.gen ^ r = algebraMap R L π ∧
      minpoly K B.gen = X ^ r - C (algebraMap R K π) ∧
      minpoly R B.gen = X ^ r - C π ∧
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) := by
  have hr : 0 < r := (Fact.out : r.Prime).pos
  let f : K[X] := X ^ r - C (algebraMap R K π)
  have hmonic : f.Monic := monic_X_pow_sub_C (algebraMap R K π) hr.ne'
  have hirr : Irreducible f :=
    X_pow_sub_C_irreducible_of_prime_parameter K π hπ r hr
  let : Fact (Irreducible f) := ⟨hirr⟩
  let L : Type v := AdjoinRoot f
  let B : PowerBasis K L := AdjoinRoot.powerBasis hmonic.ne_zero
  let : FiniteDimensional K L := B.finite
  have hdegree : Module.finrank K L = r := by
    calc
      Module.finrank K L = B.dim := B.finrank
      _ = f.natDegree := by rfl
      _ = r := natDegree_X_pow_sub_C
  have hprimitive : (primitiveRoots r K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots hr).mpr hζ⟩
  let : f.IsSplittingField K L :=
    isSplittingField_AdjoinRoot_X_pow_sub_C hprimitive hirr
  let : IsGalois K L :=
    isGalois_of_isSplittingField_X_pow_sub_C hprimitive hirr L
  have hcyclic : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K L).trans hdegree)
  have hminpolyK : minpoly K B.gen = f :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hmonic
  have hrootK : aeval B.gen f = 0 := by
    change aeval (AdjoinRoot.root f) f = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hfmap : (X ^ r - C π).map (algebraMap R K) = f := by
    simp only [f, Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  have hrootR : aeval B.gen (X ^ r - C π) = 0 := by
    rw [Polynomial.aeval_eq_aeval_map (IsScalarTower.algebraMap_eq R K L).symm,
      hfmap]
    exact hrootK
  have hintegral : IsIntegral R B.gen :=
    ⟨X ^ r - C π, monic_X_pow_sub_C π hr.ne', hrootR⟩
  have hminpolyR : minpoly R B.gen = X ^ r - C π := by
    apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hintegral, hfmap]
    exact hminpolyK
  have hpower : B.gen ^ r = algebraMap R L π := by
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hrootR
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    B, hdegree, hpower, hminpolyK, hminpolyR, inferInstance, hcyclic⟩

end ValuationTheory.DiscreteValuationField
