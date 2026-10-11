/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Tower
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.PowerBasis

/-!
# Integral elements in an Eisenstein root extension

Over a discrete valuation ring, an integral power basis with Eisenstein
minimal polynomial generates every integral element of its fraction-field
extension. Clearing polynomial denominators gives a uniformizer power
multiple in the generated ring; Eisenstein descent removes that power.

The argument does not require separability or Henselianity, and assumes no
comparison with a chosen extension valuation ring.
-/

namespace ValuationTheory.DiscreteValuationField

open scoped nonZeroDivisors Polynomial

universe u v w

variable {R : Type u} {K : Type v} {L : Type w}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]

/-- An integral power-basis generator with Eisenstein minimal polynomial
generates the integral closure of a DVR inside the extension field. -/
theorem mem_adjoin_of_isIntegral_of_minpoly_isEisensteinAt
    (B : PowerBasis K L)
    (hE : (minpoly R B.gen).IsEisensteinAt (IsLocalRing.maximalIdeal R))
    {z : L} (hz : IsIntegral R z) :
    z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
  classical
  have hB : IsIntegral R B.gen := minpoly.ne_zero_iff.mp (by
    intro hzero
    apply hE.leading
    rw [hzero, Polynomial.leadingCoeff_zero]
    exact (IsLocalRing.maximalIdeal R).zero_mem)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨f, hf⟩ := B.exists_eq_aeval' z
  let q : R[X] := IsLocalization.integerNormalization R⁰ f
  obtain ⟨c, hc, hq⟩ := IsLocalization.integerNormalization_spec R⁰ f
  have heval : Polynomial.aeval B.gen q = c • z := by
    calc
      Polynomial.aeval B.gen q =
          Polynomial.aeval B.gen (q.map (algebraMap R K)) :=
        Polynomial.aeval_eq_aeval_map
          (IsScalarTower.algebraMap_eq R K L).symm q B.gen
      _ = Polynomial.aeval B.gen ((algebraMap R K c) • f) :=
        congrArg (Polynomial.aeval B.gen : K[X] →ₐ[K] L)
          (hq.trans (IsScalarTower.algebraMap_smul K c f).symm)
      _ = (algebraMap R K c) • Polynomial.aeval B.gen f :=
        map_smul (Polynomial.aeval B.gen : K[X] →ₐ[K] L) (algebraMap R K c) f
      _ = c • z := by
        rw [IsScalarTower.algebraMap_smul, ← hf]
  have hcz : c • z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
    rw [← heval]
    exact Polynomial.aeval_mem_adjoin_singleton R B.gen
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hc) hπ
  have hpow : π ^ n • z ∈ Algebra.adjoin R ({B.gen} : Set L) := by
    have h := (Algebra.adjoin R ({B.gen} : Set L)).smul_mem hcz (↑(u⁻¹) : R)
    rw [hu, ← mul_smul, ← mul_assoc, Units.inv_mul, one_mul] at h
    exact h
  have hEπ : (minpoly R B.gen).IsEisensteinAt (Ideal.span ({π} : Set R)) := by
    rw [← hπ.maximalIdeal_eq]
    exact hE
  exact mem_adjoin_of_smul_prime_pow_smul_of_minpoly_isEisensteinAt
    (B := B) hπ.prime hB hz hpow hEπ

end ValuationTheory.DiscreteValuationField
