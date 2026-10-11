/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic

/-!
# Injectivity of prime localization maps

Proves that an injective ring map into a domain induces an injective map on localizations at a
prime and its contraction.
-/

namespace SchemeTheory

universe u v

/-- An injective coefficient map into a domain remains injective after
localization at a prime and its literal contraction. -/
theorem localRingHom_injective
    {B : Type u} {C : Type v} [CommRing B] [CommRing C] [IsDomain C]
    (Q : Ideal B) (P : Ideal C) [Q.IsPrime] [P.IsPrime]
    (f : B →+* C) (hf : Q = P.comap f) (hinj : Function.Injective f.toFun) :
    Function.Injective (Localization.localRingHom Q P f hf).toFun :=
  IsLocalization.map_injective_of_injective' Q.primeCompl C (Localization.AtPrime P)
    (Localization.le_comap_primeCompl_iff.mpr (ge_of_eq hf))
    (fun h => h P.zero_mem) hinj

end SchemeTheory
