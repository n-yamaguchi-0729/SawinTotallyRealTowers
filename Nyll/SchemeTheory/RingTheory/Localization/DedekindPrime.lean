/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Discrete valuation rings from Dedekind prime localizations

Proves that localization of a Dedekind domain at a nonzero prime is a discrete valuation ring.
-/

namespace SchemeTheory

universe u

/-- The native prime localization of a Dedekind domain is a DVR at a
nonzero prime. Its coefficient Algebra stays inside this ring-only owner. -/
theorem localizationAtPrime_isDiscreteValuationRing
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime Q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hQ (Localization.AtPrime Q)

end SchemeTheory
