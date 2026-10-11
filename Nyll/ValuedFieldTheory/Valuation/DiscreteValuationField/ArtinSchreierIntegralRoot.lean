/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ArtinSchreierEisenstein
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.AdjoinRoot

/-!
# The integral minimal polynomial of the actual reciprocal root

The standard `AdjoinRoot` of the fraction-field Eisenstein polynomial
already has its canonical coefficient-ring algebra. Its root is integral
because it annihilates the displayed monic coefficient-ring polynomial.
Comparing minimal polynomials through the fraction field identifies its
integral minimal polynomial with that polynomial, without any valuation
or Henselianity assumption.
-/


namespace ValuationTheory.DiscreteValuationField

open Polynomial
open scoped Polynomial

universe u v

/-- The actual adjoined reciprocal root has the displayed integral minimal
polynomial. Irreducibility and the root equation are constructed here. -/
theorem minpoly_artinSchreierAdjoinRoot
    (R : Type u) (K : Type v)
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Prime π) (n : ℕ) (hn : 1 < n) :
    minpoly R
      (AdjoinRoot.root
        ((artinSchreierInversePolynomial π n).map (algebraMap R K))) =
      artinSchreierInversePolynomial π n := by
  let f : R[X] := artinSchreierInversePolynomial π n
  let fK : K[X] := f.map (algebraMap R K)
  have hmonic : f.Monic := artinSchreierInversePolynomial_monic π n hn
  have hmonicK : fK.Monic := hmonic.map (algebraMap R K)
  have hirr : Irreducible fK :=
    artinSchreierInversePolynomial_map_irreducible K π hπ n hn
  let : Fact (Irreducible fK) := ⟨hirr⟩
  have hrootR : aeval (AdjoinRoot.root fK) f = 0 := by
    rw [AdjoinRoot.aeval_eq_of_algebra]
    exact AdjoinRoot.mk_self
  have hint : IsIntegral R (AdjoinRoot.root fK) := ⟨f, hmonic, hrootR⟩
  have hrootK : aeval (AdjoinRoot.root fK) fK = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  change minpoly R (AdjoinRoot.root fK) = f
  apply Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hint]
  exact (minpoly.eq_of_irreducible_of_monic hirr hrootK hmonicK).symm

end ValuationTheory.DiscreteValuationField
