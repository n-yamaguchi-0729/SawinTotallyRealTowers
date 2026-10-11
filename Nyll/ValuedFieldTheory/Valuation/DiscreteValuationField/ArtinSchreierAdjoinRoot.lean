/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierEisenstein
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierPolynomial
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.PowerBasis

/-!
# A cyclic Artin--Schreier extension from an Eisenstein parameter

The extension is the actual `AdjoinRoot` of the irreducible reciprocal
polynomial. Its standard power basis supplies the degree. The inverse
root generates the same algebra, satisfies the Artin--Schreier equation,
and supplies a splitting field using prime-field translates.

All instances in the construction come from this polynomial or its power
basis. No extension degree, Galois property, or valuation comparison is an
input. The output power basis and its minimal polynomial are retained for
the later Eisenstein residue-field comparison.
-/


namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v

/-- A prime parameter in an integrally closed domain produces an actual
cyclic degree-`p` extension of its characteristic-`p` fraction field. The
power-basis generator is the inverse of the Artin--Schreier generator. -/
theorem exists_cyclic_artinSchreier_extension_of_prime_parameter
    (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Prime π) (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra K L)
      (B : PowerBasis K L) (α : L),
      Module.finrank K L = p ∧
      B.gen = α⁻¹ ∧
      α ^ p - α = algebraMap K L ((algebraMap R K π)⁻¹) ∧
      Algebra.adjoin K ({α} : Set L) = ⊤ ∧
      minpoly K B.gen =
        (artinSchreierInversePolynomial π p).map (algebraMap R K) ∧
      IsGalois K L ∧ IsCyclic (L ≃ₐ[K] L) := by
  let f : K[X] :=
    (artinSchreierInversePolynomial π p).map (algebraMap R K)
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hmonic : f.Monic :=
    (artinSchreierInversePolynomial_monic π p hp).map (algebraMap R K)
  let : Fact (Irreducible f) :=
    ⟨artinSchreierInversePolynomial_map_irreducible K π hπ p hp⟩
  let L : Type v := AdjoinRoot f
  let B : PowerBasis K L := AdjoinRoot.powerBasis hmonic.ne_zero
  let β : L := B.gen
  let α : L := β⁻¹
  let a : K := (algebraMap R K π)⁻¹
  let q : K[X] := artinSchreierPolynomial p a
  let : FiniteDimensional K L := B.finite
  let : CharP L p :=
    charP_of_injective_algebraMap (algebraMap K L).injective p
  have hdegree : Module.finrank K L = p := by
    calc
      Module.finrank K L = B.dim := B.finrank
      _ = f.natDegree := by rfl
      _ = p := by
        change ((artinSchreierInversePolynomial π p).map (algebraMap R K)).natDegree = p
        rw [(artinSchreierInversePolynomial_monic π p hp).natDegree_map,
          artinSchreierInversePolynomial_natDegree π p hp]
  have hβroot : aeval β f = 0 := by
    change aeval (AdjoinRoot.root f) f = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hfmap : f = artinSchreierInversePolynomial (algebraMap R K π) p := by
    simp only [f, artinSchreierInversePolynomial, Polynomial.map_sub,
      Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, map_X, map_C]
  have hπK : algebraMap R K π ≠ 0 := by
    intro hzero
    apply hπ.ne_zero
    exact (IsFractionRing.injective R K)
      (hzero.trans (map_zero (algebraMap R K)).symm)
  have hα : α ^ p - α = algebraMap K L a :=
    artinSchreier_eq_of_inversePolynomial_root (algebraMap R K π) hπK p hp β
      (hfmap ▸ hβroot)
  have hαintegral : IsIntegral K α := B.isIntegral_gen.inv
  have hβeq : α⁻¹ = B.gen := by
    change (B.gen⁻¹)⁻¹ = B.gen
    exact inv_inv B.gen
  have hβmem : B.gen ∈ Algebra.adjoin K ({α} : Set L) := by
    rw [← hβeq]
    exact hαintegral.inv_mem_adjoin
  have hαgen : Algebra.adjoin K ({α} : Set L) = ⊤ :=
    PowerBasis.adjoin_eq_top_of_gen_mem_adjoin (B := B) hβmem
  have hqsep : q.Separable := artinSchreierPolynomial_separable p a
  have hqroot : aeval α q = 0 := by
    simp only [q, artinSchreierPolynomial, map_sub, map_pow, aeval_X, aeval_C,
      hα, sub_self]
  have hqsplit : (q.map (algebraMap K L)).Splits := by
    simpa only [q, artinSchreierPolynomial, Polynomial.map_sub,
      Polynomial.map_pow, map_X, map_C] using
      artinSchreierPolynomial_splits_of_root p (algebraMap K L a) α hα
  have hαmem : α ∈ q.rootSet L := (mem_rootSet_of_ne hqsep.ne_zero).mpr hqroot
  have hqgen : Algebra.adjoin K (q.rootSet L) = ⊤ := by
    apply top_unique
    rw [← hαgen]
    exact Algebra.adjoin_mono (Set.singleton_subset_iff.mpr hαmem)
  let : q.IsSplittingField K L := ⟨hqsplit, hqgen⟩
  let : IsGalois K L := IsGalois.of_separable_splitting_field hqsep
  have hcyclic : IsCyclic (L ≃ₐ[K] L) :=
    isCyclic_of_prime_card ((IsGalois.card_aut_eq_finrank K L).trans hdegree)
  have hminpoly : minpoly K B.gen = f :=
    AdjoinRoot.minpoly_powerBasis_gen_of_monic hmonic
  refine ⟨L, inferInstance, inferInstance, B, α, hdegree, ?_, hα,
    hαgen, hminpoly, inferInstance, hcyclic⟩
  change β = (β⁻¹)⁻¹
  exact (inv_inv β).symm

end ValuationTheory.DiscreteValuationField
