/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueExtensionPrimitive

/-!
# Galois invariance of extensions of Henselian discrete valuations

Every base-field automorphism of a finite extension preserves the actual
extension valuation. Henselianity supplies uniqueness of the valuation ring;
the finite order of the automorphism then forces equality of values.
-/

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

universe u v w z

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Automorphisms of a finite extension preserve its chosen extension valuation. -/
theorem valuation_algEquiv_eq [FiniteDimensional K L]
    (base : HenselianDVF.{u, v} K) (target : DVF.{w, z} L)
    [base.toDVF.valuation.HasExtension target.valuation]
    (f : L ≃ₐ[K] L) (x : L) : target.valuation (f x) = target.valuation x := by
  let V : ValuationSubring K := base.toDVF.valuation.valuationSubring
  let W : ValuationSubring L := target.valuation.valuationSubring
  have hW : V.valuation.HasExtension W.valuation := by
    apply _root_.Valuation.HasExtension.ofComapInteger
    ext a
    change W.valuation (algebraMap K L a) ≤ 1 ↔ V.valuation a ≤ 1
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    exact _root_.Valuation.HasExtension.val_map_le_one_iff
      base.toDVF.valuation target.valuation a
  have huniq : ∀ W' : ValuationSubring L,
      V.valuation.HasExtension W'.valuation → W' = W := by
    intro W' hW'
    have : V.valuation.HasExtension W.valuation := hW
    have : V.valuation.HasExtension W'.valuation := hW'
    simpa only [ValuationSubring.valuationSubring_valuation] using
      ValuationTheory.Henselian.valuationSubring_eq_of_henselianRing
        V W'.valuation W.valuation
  have hval : W.valuation (f x) = W.valuation x :=
    AlgebraicNumberTheory.Valuations.valuation_algEquiv_eq_of_unique_extension_of_finiteDimensional
      V W hW huniq f x
  exact (_root_.Valuation.isEquiv_valuation_valuationSubring target.valuation).eq_iff.mpr hval

end ValuationTheory.DiscreteValuationField.HenselianDVF
