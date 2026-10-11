/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Galois isometries over a Henselian normed field

The norm of a finite extension is preserved by every base-field automorphism
when the nonarchimedean base valuation ring is Henselian. Completeness of the
base field is not required.
-/

namespace ValuationTheory.Henselian

variable {K L : Type*} [NormedField K] [NormedField L]
  [IsUltrametricDist K] [IsUltrametricDist L] [NormedAlgebra K L]

private theorem normed_valuationSubring_hasExtension :
    (NormedField.valuation (K := K)).valuationSubring.valuation.HasExtension
      (NormedField.valuation (K := L)).valuationSubring.valuation where
  val_isEquiv_comap := by
    rw [Valuation.isEquiv_iff_val_le_one]
    intro x
    change (NormedField.valuation (K := K)).valuationSubring.valuation x ≤ 1 ↔
      (NormedField.valuation (K := L)).valuationSubring.valuation
        (algebraMap K L x) ≤ 1
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    change ‖x‖₊ ≤ 1 ↔ ‖algebraMap K L x‖₊ ≤ 1
    rw [nnnorm_algebraMap']

/-- Every automorphism of a finite normed extension of a Henselian
nonarchimedean field preserves the norm. -/
theorem norm_algEquiv_eq_of_henselianRing [FiniteDimensional K L]
    [HenselianRing (NormedField.valuation (K := K)).valuationSubring
      (IsLocalRing.maximalIdeal (NormedField.valuation (K := K)).valuationSubring)]
    (σ : L ≃ₐ[K] L) (x : L) : ‖σ x‖ = ‖x‖ := by
  let V : ValuationSubring K := (NormedField.valuation (K := K)).valuationSubring
  let W : ValuationSubring L := (NormedField.valuation (K := L)).valuationSubring
  have hW : V.valuation.HasExtension W.valuation :=
    normed_valuationSubring_hasExtension (K := K) (L := L)
  have huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W := by
    intro W' hW'
    have : V.valuation.HasExtension W.valuation := hW
    have : V.valuation.HasExtension W'.valuation := hW'
    simpa only [ValuationSubring.valuationSubring_valuation] using
      valuationSubring_eq_of_henselianRing V W'.valuation W.valuation
  have hval : W.valuation (σ x) = W.valuation x :=
    AlgebraicNumberTheory.Valuations.valuation_algEquiv_eq_of_unique_extension_of_finiteDimensional
      V W hW huniq σ x
  have hnorm : ‖σ x‖₊ = ‖x‖₊ :=
    (Valuation.isEquiv_valuation_valuationSubring
      (NormedField.valuation (K := L))).eq_iff.mpr hval
  exact congrArg (fun r : NNReal => (r : ℝ)) hnorm

end ValuationTheory.Henselian
