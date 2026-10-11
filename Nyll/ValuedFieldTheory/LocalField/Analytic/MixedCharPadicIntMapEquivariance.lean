/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMapContinuous
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationPreservingContinuous
import Mathlib.Topology.DenseEmbedding

/-!
# Automorphism invariance of the p-adic integer map

A valuation-preserving field automorphism fixes the constructed image of
the p-adic integers, by continuity and density of the natural numbers.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K]

/-- Valuation-preserving automorphisms fix every scalar in the actual p-adic image. -/
theorem ringEquiv_padicIntToFieldOfMixedChar
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (f : K ≃+* K) (hval : ∀ x : K, v (f x) = v x) (a : ℤ_[p]) :
    f (padicIntToFieldOfMixedChar v p a) = padicIntToFieldOfMixedChar v p a := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  have hmap : Continuous (padicIntToFieldOfMixedChar v p) :=
    continuous_padicIntToFieldOfMixedChar v p
  have hf : Continuous f :=
    ValuationTheory.DiscreteValuationField.Valuation.continuous_ringEquiv_of_preserves v f hval
  refine PadicInt.denseRange_natCast.induction_on a (isClosed_eq (hf.comp hmap) hmap) ?_
  intro n
  simp only [map_natCast]

/-- The field action commutes with multiplication by the constructed p-adic scalars. -/
theorem ringEquiv_padicIntToFieldOfMixedChar_mul
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (f : K ≃+* K) (hval : ∀ x : K, v (f x) = v x) (a : ℤ_[p]) (x : K) :
    f (padicIntToFieldOfMixedChar v p a * x) = padicIntToFieldOfMixedChar v p a * f x := by
  rw [f.map_mul, ringEquiv_padicIntToFieldOfMixedChar v p f hval a]

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
