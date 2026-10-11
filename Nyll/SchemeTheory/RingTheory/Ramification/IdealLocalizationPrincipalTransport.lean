/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.IdealLocalizationFieldAction
import Nyll.SchemeTheory.RingTheory.Ramification.ConjugateRingAction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.PrincipalUnitRingTransport

/-!
# Principal-unit actions on localized valuation rings

Transports a prime-localization automorphism acting by principal-unit multipliers to the
corresponding valuation ring. The transported automorphism retains its compatible ambient field
action.
-/

noncomputable section

namespace TameAbhyankar.SGA1

universe u v

/-- Transport the actual native prime-localization action through its
canonical valuation-ring equivalence. Both the target automorphism and its
field square are constructed; no localized comparison is supplied. -/
theorem idealLocalization_exists_principal_valuation_action
    (B : Type u) (L : Type v) [CommRing B] [IsDedekindDomain B]
    [Field L] [Algebra B L] [IsFractionRing B L]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (σ : B ≃+* B) (hσ : Q = Q.comap σ.toRingHom) (ρ : L →+* L)
    (hcoeff : ρ.comp (algebraMap B L) = (algebraMap B L).comp σ.toRingHom)
    (hprincipal : ∀ x : Localization.AtPrime Q, ∃ a : (Localization.AtPrime Q)ˣ,
      Localization.localRingEquiv Q Q σ hσ x = x * (a : Localization.AtPrime Q) ∧
        (a : Localization.AtPrime Q) - 1 ∈ IsLocalRing.maximalIdeal (Localization.AtPrime Q)) :
    ∃ τ : idealLocalizationValuationSubring B L Q hQ ≃+*
        idealLocalizationValuationSubring B L Q hQ,
      (idealLocalizationValuationSubring B L Q hQ).subtype.comp τ.toRingHom =
        ρ.comp (idealLocalizationValuationSubring B L Q hQ).subtype ∧
      ∀ x : idealLocalizationValuationSubring B L Q hQ,
        ∃ a : (idealLocalizationValuationSubring B L Q hQ)ˣ,
          τ.toRingHom x = x * (a : idealLocalizationValuationSubring B L Q hQ) ∧
            (a : idealLocalizationValuationSubring B L Q hQ) - 1 ∈
              IsLocalRing.maximalIdeal (idealLocalizationValuationSubring B L Q hQ) := by
  let e := primeLocalizationEquivValuation B L Q hQ
  let s := Localization.localRingEquiv Q Q σ hσ
  let τ := e.symm.trans (s.trans e)
  refine ⟨τ, ?_, ?_⟩
  · exact SchemeTheory.ringEquiv_conjugate_field_square e s
      (idealLocalizationValuationSubring B L Q hQ).subtype ρ
      (primeLocalizationEquivValuation_field_square B L Q hQ σ hσ ρ hcoeff)
  · exact RamificationTheory.HilbertRamification.LocalRing.principalUnitMultipliers_transport
      e s.toRingHom τ.toRingHom (SchemeTheory.ringEquiv_conjugate_commutes e s) hprincipal

end TameAbhyankar.SGA1
