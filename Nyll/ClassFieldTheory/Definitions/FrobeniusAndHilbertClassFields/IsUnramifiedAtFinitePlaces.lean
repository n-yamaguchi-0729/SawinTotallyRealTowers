/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.NumberTheory.RamificationInertia.Unramified

/-!
# Unramifiedness at all finite places
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTheory

universe u v

/-- Finite-place unramifiedness is formal unramifiedness of the integer rings. -/
abbrev IsUnramifiedAtFinitePlaces
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] : Prop :=
  Algebra.FormallyUnramified (𝓞 K) (𝓞 L)

namespace IsUnramifiedAtFinitePlaces

/-- Nonzero primes upstairs suffice: the zero prime is unramified in characteristic zero. -/
theorem iff_forall_above
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsUnramifiedAtFinitePlaces K L ↔
      ∀ P : HeightOneSpectrum (𝓞 L), Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := by
  change Algebra.FormallyUnramified (𝓞 K) (𝓞 L) ↔ _
  rw [Algebra.formallyUnramified_iff_forall]
  constructor
  · intro h P
    exact h ⟨P.asIdeal, P.isPrime⟩
  · intro h q
    by_cases hq : q.asIdeal = ⊥
    · simpa only [hq] using
        (Algebra.isUnramifiedAt_bot (R := 𝓞 K) (S := 𝓞 L))
    · exact h ⟨q.asIdeal, q.isPrime, hq⟩

/-- Formal unramifiedness supplies the local condition at any finite prime upstairs. -/
theorem atPrime
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (h : IsUnramifiedAtFinitePlaces K L) (P : HeightOneSpectrum (𝓞 L)) :
    Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal :=
  (iff_forall_above K L).mp h P

end IsUnramifiedAtFinitePlaces

end ClassFieldTheory
