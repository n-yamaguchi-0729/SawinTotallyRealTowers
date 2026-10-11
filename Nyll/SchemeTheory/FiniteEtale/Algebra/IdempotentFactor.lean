/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Étale idempotent factors

The quotient imposing `e = 1` for an idempotent `e` is localization at `e`.
Consequently, an idempotent factor of an étale algebra is again étale over
the original base, with the canonical quotient algebra structure.
-/

@[expose] public section

universe u v

namespace Algebra.Etale

/-- The factor on which an idempotent becomes `1` is étale over the base. -/
theorem quotient_one_sub_of_isIdempotentElem
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.Etale R B] (e : B) (he : IsIdempotentElem e) :
    Algebra.Etale R (B ⧸ Ideal.span {1 - e}) := by
  let : IsLocalization.Away e (B ⧸ Ideal.span {1 - e}) :=
    IsLocalization.away_of_isIdempotentElem he
      (show RingHom.ker (algebraMap B (B ⧸ Ideal.span {1 - e})) =
        Ideal.span {1 - e} from Ideal.mk_ker)
      Ideal.Quotient.mk_surjective
  let : Algebra.Etale B (B ⧸ Ideal.span {1 - e}) :=
    Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Etale.comp R B (B ⧸ Ideal.span {1 - e})

end Algebra.Etale
