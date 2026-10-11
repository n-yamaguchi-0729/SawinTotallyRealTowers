/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Commuting squares after prime localization

Proves that a commuting square of ring maps induces a commuting square on prime localizations
when the relevant primes are preserved.
-/

namespace SchemeTheory

universe u v

/-- A commuting square of actual coefficient maps remains commuting after
localization at the preserved primes. This uses only the existing localRingHom
construction and does not install any group action on either ring. -/
theorem primeLocalization_commuting_square
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (P : Ideal A) [P.IsPrime] (Q : Ideal B) [Q.IsPrime]
    (f : A →+* B) (s : A →+* A) (t : B →+* B)
    (hf : P = Q.comap f) (hs : P = P.comap s) (ht : Q = Q.comap t)
    (hcomm : f.comp s = t.comp f) :
    (Localization.localRingHom P Q f hf).comp (Localization.localRingHom P P s hs) =
      (Localization.localRingHom Q Q t ht).comp (Localization.localRingHom P Q f hf) := by
  apply IsLocalization.ringHom_ext P.primeCompl
  apply RingHom.ext
  intro a
  change Localization.localRingHom P Q f hf
      (Localization.localRingHom P P s hs (algebraMap A (Localization.AtPrime P) a)) =
    Localization.localRingHom Q Q t ht
      (Localization.localRingHom P Q f hf (algebraMap A (Localization.AtPrime P) a))
  rw [Localization.localRingHom_to_map, Localization.localRingHom_to_map,
    Localization.localRingHom_to_map, Localization.localRingHom_to_map]
  exact congrArg (algebraMap B (Localization.AtPrime Q)) (RingHom.congr_fun hcomm a)

end SchemeTheory
