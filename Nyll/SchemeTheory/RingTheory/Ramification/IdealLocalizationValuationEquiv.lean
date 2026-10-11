/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization
import Mathlib.RingTheory.Localization.Basic

/-!
# Prime localization and its valuation-ring model

Constructs the canonical ring equivalence between a Dedekind prime localization and its
valuation-ring model in the fraction field. Computation lemmas identify its values on the
original coefficients.
-/

noncomputable section

namespace TameAbhyankar.SGA1

universe u v

variable (B : Type u) (L : Type v) [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)

local instance idealLocalizationValuationAlgebra :
    Algebra B (idealLocalizationValuationSubring B L Q hQ) := by
  change Algebra B (idealLocalizationSubalgebra B L Q)
  infer_instance

private theorem idealLocalizationValuation_isLocalization :
    IsLocalization.AtPrime (idealLocalizationValuationSubring B L Q hQ) Q := by
  change IsLocalization.AtPrime (idealLocalizationSubalgebra B L Q) Q
  infer_instance

/-- The canonical identity-on-coefficients equivalence from the literal
prime localization to the already constructed native local valuation ring. -/
def primeLocalizationEquivValuation :
    Localization.AtPrime Q ≃+* idealLocalizationValuationSubring B L Q hQ := by
  have : IsLocalization.AtPrime (idealLocalizationValuationSubring B L Q hQ) Q :=
    idealLocalizationValuation_isLocalization B L Q hQ
  exact (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (idealLocalizationValuationSubring B L Q hQ)).toRingEquiv

/-- The constructed equivalence uses the actual original normalization
coefficient map. -/
theorem primeLocalizationEquivValuation_algebraMap (b : B) :
    primeLocalizationEquivValuation B L Q hQ
        (algebraMap B (Localization.AtPrime Q) b) =
      algebraMap B (idealLocalizationValuationSubring B L Q hQ) b := by
  have : IsLocalization.AtPrime (idealLocalizationValuationSubring B L Q hQ) Q :=
    idealLocalizationValuation_isLocalization B L Q hQ
  exact (IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q)
    (idealLocalizationValuationSubring B L Q hQ)).commutes b

/-- The canonical equivalence followed by the actual field inclusion is the
original B-coefficient map. Its interface opens no B-action on the target V. -/
theorem primeLocalizationEquivValuation_algebraMap_coe (b : B) :
    (primeLocalizationEquivValuation B L Q hQ
      (algebraMap B (Localization.AtPrime Q) b) : L) = algebraMap B L b := by
  rw [primeLocalizationEquivValuation_algebraMap]
  rfl

end TameAbhyankar.SGA1
