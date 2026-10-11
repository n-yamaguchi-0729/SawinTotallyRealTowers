/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Unramified.MaximalSubextension
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# Tame ramification for algebraic valued extensions

Suppose that the residue characteristic `p = char(kappa)` is positive.  An
algebraic valued extension `L/K` is tamely ramified when its residue extension
is separable and `[L : T]` is prime to `p`, where `T/K` is the maximal
unramified subextension.  For an infinite extension, the
degree condition means that every finite intermediate extension of `L/T` has
degree prime to `p`.

The definitions below use the characteristic of the actual residue field of
the valuation on `K`; there is no independent natural-number parameter that
could be filled by an unrelated prime.
-/

noncomputable section

universe u v

namespace AlgebraicNumberTheory
namespace Valuations

section TamelyRamifiedExtensions

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The actual residue characteristic `p = char(kappa)` used in the tame
ramification predicate. -/
def residueCharacteristic (v : LubinTate.Valuations.ExponentialValuation K) : ℕ :=
  ringChar (IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v))

/-- Positive residue characteristic is exactly the nonvanishing of the
actual residue characteristic. -/
def PositiveResidueCharacteristic
    (v : LubinTate.Valuations.ExponentialValuation K) : Prop :=
  residueCharacteristic v ≠ 0

/-- In positive residue characteristic, the actual residue characteristic is
prime.  Thus later uses may obtain `Fact p.Prime` from the positivity clause
of the tame-ramification predicate rather than assume an unrelated certificate. -/
theorem residueCharacteristic_prime
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hp : PositiveResidueCharacteristic v) :
    Nat.Prime (residueCharacteristic v) := by
  let κ := IsLocalRing.ResidueField (LubinTate.Valuations.exponentialValuationSubring v)
  change Nat.Prime (ringChar κ)
  exact CharP.char_prime_of_ne_zero κ hp

/-- A `Fact` form of `residueCharacteristic_prime`, for APIs which take
primality through typeclass inference. -/
theorem residueCharacteristicPrimeFact
    (v : LubinTate.Valuations.ExponentialValuation K)
    (hp : PositiveResidueCharacteristic v) :
    Fact (Nat.Prime (residueCharacteristic v)) :=
  ⟨residueCharacteristic_prime v hp⟩

/-- The infinite-degree clause for tame ramification: every finite
intermediate extension of `L/T` has degree prime to `p`.

Finiteness is supplied by the quantified datum `hE`; it is not an ambient
finite-dimensionality assumption hidden in the definition. -/
def FiniteSubextensionDegreesPrimeTo
    (T : IntermediateField K L) (p : ℕ) : Prop :=
  ∀ (E : IntermediateField T L) (hE : FiniteDimensional T E),
    letI : FiniteDimensional T E := hE
    Nat.Coprime (Module.finrank T E) p

/-- For a finite ambient extension, the infinite-extension clause is
equivalent to the single condition that `[L : T]` is prime to `p`. -/
theorem finiteSubextensionDegreesPrimeTo_iff
    [FiniteDimensional K L]
    (T : IntermediateField K L) (p : ℕ) :
    FiniteSubextensionDegreesPrimeTo T p ↔
      Nat.Coprime (Module.finrank T L) p := by
  constructor
  · intro h
    have htop := h (⊤ : IntermediateField T L) inferInstance
    simpa using htop
  · intro h E hE
    let : FiniteDimensional T E := hE
    apply Nat.Coprime.of_dvd_left _ h
    have hdvd :
        Module.finrank T E ∣
          Module.finrank T (⊤ : IntermediateField T L) :=
      IntermediateField.finrank_dvd_of_le_right (show E ≤ ⊤ from le_top)
    simpa using hdvd

/-- Tame ramification for a finite extension.

Here `T` is the actual maximal unramified subextension
and `p` is the actual residue characteristic of `K`.  The positivity clause
records the standing condition `p > 0`; under that clause the two
remaining conjuncts are exactly residue separability and `([L : T], p) = 1`.
-/
def FiniteTamelyRamifiedExtension
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : Prop :=
  PositiveResidueCharacteristic v ∧
    ResidueExtensionIsSeparable v w hExt ∧
      Nat.Coprime
        (Module.finrank (maximalUnramifiedSubextension v w hExt) L)
        (residueCharacteristic v)

/-- Tame ramification for an arbitrary algebraic extension.

The finite-degree clause requires every finite
intermediate extension of `L/T` has degree prime to the actual positive
residue characteristic. -/
def AlgebraicTamelyRamifiedExtension
    [Algebra.IsAlgebraic K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) : Prop :=
  PositiveResidueCharacteristic v ∧
    ResidueExtensionIsSeparable v w hExt ∧
      FiniteSubextensionDegreesPrimeTo
        (maximalUnramifiedSubextension v w hExt)
        (residueCharacteristic v)

/-- On finite extensions the finite and arbitrary-algebraic tame-ramification
predicates agree. -/
theorem finiteTamelyRamifiedExtension_iff_algebraic
    [FiniteDimensional K L]
    (v : LubinTate.Valuations.ExponentialValuation K)
    (w : LubinTate.Valuations.ExponentialValuation L)
    (hExt : ∀ a : K, w (algebraMap K L a) = v a) :
    FiniteTamelyRamifiedExtension v w hExt ↔
      AlgebraicTamelyRamifiedExtension v w hExt := by
  rw [FiniteTamelyRamifiedExtension,
    AlgebraicTamelyRamifiedExtension,
    finiteSubextensionDegreesPrimeTo_iff]

end TamelyRamifiedExtensions

end Valuations
end AlgebraicNumberTheory

end
