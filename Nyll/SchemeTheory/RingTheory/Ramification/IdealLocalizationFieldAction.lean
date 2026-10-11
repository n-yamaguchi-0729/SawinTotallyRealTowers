/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.IdealLocalizationValuationEquiv
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Field compatibility of prime-localization automorphisms

Proves that a prime-localization automorphism, viewed through the canonical valuation-ring
equivalence, agrees with a compatible ambient field action on coefficients.
-/

noncomputable section

namespace TameAbhyankar.SGA1

universe u v

/-- The native prime-localization automorphism has the prescribed original
field action. Equality is proved on actual B-coefficients and then extended
through localization; no localized action comparison is an input. -/
theorem primeLocalizationEquivValuation_field_square
    (B : Type u) (L : Type v) [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (σ : B ≃+* B) (hσ : Q = Q.comap σ.toRingHom)
    (ρ : L →+* L)
    (hcoeff : ρ.comp (algebraMap B L) = (algebraMap B L).comp σ.toRingHom) :
    ((idealLocalizationValuationSubring B L Q hQ).subtype.comp
      (primeLocalizationEquivValuation B L Q hQ).toRingHom).comp
        (Localization.localRingEquiv Q Q σ hσ).toRingHom =
      ρ.comp ((idealLocalizationValuationSubring B L Q hQ).subtype.comp
        (primeLocalizationEquivValuation B L Q hQ).toRingHom) := by
  apply IsLocalization.ringHom_ext Q.primeCompl
  apply RingHom.ext
  intro b
  change (primeLocalizationEquivValuation B L Q hQ
      (Localization.localRingHom Q Q σ.toRingHom hσ
        (algebraMap B (Localization.AtPrime Q) b)) : L) =
    ρ (primeLocalizationEquivValuation B L Q hQ
      (algebraMap B (Localization.AtPrime Q) b) : L)
  rw [Localization.localRingHom_to_map,
    primeLocalizationEquivValuation_algebraMap_coe,
    primeLocalizationEquivValuation_algebraMap_coe]
  exact (RingHom.congr_fun hcoeff b).symm

end TameAbhyankar.SGA1
