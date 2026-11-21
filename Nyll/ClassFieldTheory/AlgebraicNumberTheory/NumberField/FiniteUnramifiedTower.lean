/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.FinitePlaceContraction
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions

/-!
# Finite-prime unramifiedness in towers of number fields

This file records the tower properties of being unramified at every
finite prime.  The transitivity and intermediate-field arguments are
proved from multiplicativity of ramification indices.
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

attribute [local instance] Ideal.Quotient.field

universe u v w

namespace ClassFieldTheory.IsUnramifiedAtFinitePlaces

/-- The same integer-ring condition may be checked at all nonzero base primes. -/
theorem iff_forall_below
    (K : Type u) (L : Type v)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsUnramifiedAtFinitePlaces K L ↔
      ∀ v : HeightOneSpectrum (𝓞 K), Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal := by
  constructor
  · intro h v P hP hOver
    exact h.atPrime
      ⟨P, hP, @Ideal.ne_bot_of_liesOver_of_ne_bot
        (𝓞 K) (𝓞 L) _ _ _ _ v.asIdeal v.ne_bot P hOver⟩
  · intro h
    apply (iff_forall_above K L).mpr
    intro W
    exact h (finitePlaceBelow (K := K) W) W.asIdeal W.isPrime ⟨rfl⟩

/-- Formal unramifiedness supplies the condition over a finite base prime. -/
theorem atBasePrime
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (h : IsUnramifiedAtFinitePlaces K L) (v : HeightOneSpectrum (𝓞 K)) :
    Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal :=
  (iff_forall_below K L).mp h v

/-- The identity extension is unramified at every finite place. -/
theorem refl
    (K : Type u) [Field K] [NumberField K] :
    IsUnramifiedAtFinitePlaces K K := by
  change Algebra.FormallyUnramified (𝓞 K) (𝓞 K)
  infer_instance

variable
    {k : Type u} {K : Type v} {F : Type w}
    [Field k] [NumberField k]
    [Field K] [NumberField K]
    [Field F] [NumberField F]
    [Algebra k K] [Algebra k F] [Algebra K F]
    [IsScalarTower k K F]

/-- Finite-prime unramifiedness is transitive in a tower of number
fields. -/
theorem trans
    (hkK : IsUnramifiedAtFinitePlaces k K)
    (hKF : IsUnramifiedAtFinitePlaces K F) :
    IsUnramifiedAtFinitePlaces k F := by
  apply (iff_forall_above k F).mpr
  intro P
  let p : HeightOneSpectrum (𝓞 K) :=
    finitePlaceBelow (K := K) P
  let hPp : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  let : Module.Finite (𝓞 k) (𝓞 K) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := K)
  let : Module.Finite (𝓞 K) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := K) (L := F)
  let : Module.Finite (𝓞 k) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := F)
  let hkKp :
      Algebra.IsUnramifiedAt (𝓞 k) p.asIdeal :=
    hkK.atPrime p
  let hKFP :
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal :=
    hKF.atPrime P
  have hLower :
      p.asIdeal.ramificationIdx (𝓞 k) = 1 :=
    Ideal.ramificationIdx_eq_one p.asIdeal (𝓞 k)
  have hUpper :
      P.asIdeal.ramificationIdx (𝓞 K) = 1 :=
    Ideal.ramificationIdx_eq_one P.asIdeal (𝓞 K)
  have hTower :
      P.asIdeal.ramificationIdx (𝓞 k) =
        p.asIdeal.ramificationIdx (𝓞 k) *
          P.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower
      (R := 𝓞 k) p.asIdeal P.asIdeal
  have hTop :
      P.asIdeal.ramificationIdx (𝓞 k) = 1 := by
    rw [hTower, hLower, hUpper, one_mul]
  have hBasePrime :
      P.asIdeal.under (𝓞 k) ≠ ⊥ := by
    simpa only [finitePlaceBelow_asIdeal] using
      (finitePlaceBelow (K := k) P).ne_bot
  let : Finite ((𝓞 k) ⧸ P.asIdeal.under (𝓞 k)) :=
    Ring.HasFiniteQuotients.finiteQuotient hBasePrime
  let :
      PerfectField (P.asIdeal.under (𝓞 k)).ResidueField :=
    PerfectField.ofFinite
  exact
    (Ideal.ramificationIdx_eq_one_iff
      (R := 𝓞 k) (S := 𝓞 F) (q := P.asIdeal)).1 hTop

/-- If the top of a number-field tower is unramified over the bottom,
then it is unramified over the intermediate field. -/
theorem top
    (hkF : IsUnramifiedAtFinitePlaces k F) :
    IsUnramifiedAtFinitePlaces K F := by
  let := hkF
  exact Algebra.FormallyUnramified.of_restrictScalars (𝓞 k) (𝓞 K) (𝓞 F)

/-- If the top of a number-field tower is unramified over the bottom,
then the intermediate field is unramified over the bottom. -/
theorem bot
    (hkF : IsUnramifiedAtFinitePlaces k F) :
    IsUnramifiedAtFinitePlaces k K := by
  apply (iff_forall_above k K).mpr
  intro p
  let : Module.Finite (𝓞 k) (𝓞 K) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := K)
  let : Module.Finite (𝓞 K) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := K) (L := F)
  let : Module.Finite (𝓞 k) (𝓞 F) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
      (K := k) (L := F)
  obtain ⟨⟨P, hPprime, hPp⟩⟩ :=
    p.asIdeal.nonempty_primesOver (S := 𝓞 F)
  let : P.IsPrime := hPprime
  let : P.LiesOver p.asIdeal := hPp
  have hPne : P ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P
  let P' : HeightOneSpectrum (𝓞 F) :=
    { asIdeal := P
      isPrime := hPprime
      ne_bot := hPne }
  let :
      Algebra.IsUnramifiedAt (𝓞 k) P :=
    hkF.atPrime P'
  have hTop :
      P.ramificationIdx (𝓞 k) = 1 :=
    Ideal.ramificationIdx_eq_one P (𝓞 k)
  have hTower :
      P.ramificationIdx (𝓞 k) =
        p.asIdeal.ramificationIdx (𝓞 k) *
          P.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_tower
      (R := 𝓞 k) p.asIdeal P
  have hLower :
      p.asIdeal.ramificationIdx (𝓞 k) = 1 :=
    (mul_eq_one.mp (hTower.symm.trans hTop)).1
  have hBasePrime :
      p.asIdeal.under (𝓞 k) ≠ ⊥ := by
    simpa only [finitePlaceBelow_asIdeal] using
      (finitePlaceBelow (K := k) p).ne_bot
  let : Finite ((𝓞 k) ⧸ p.asIdeal.under (𝓞 k)) :=
    Ring.HasFiniteQuotients.finiteQuotient hBasePrime
  let :
      PerfectField (p.asIdeal.under (𝓞 k)).ResidueField :=
    PerfectField.ofFinite
  exact
    (Ideal.ramificationIdx_eq_one_iff
      (R := 𝓞 k) (S := 𝓞 K) (q := p.asIdeal)).1 hLower

end ClassFieldTheory.IsUnramifiedAtFinitePlaces
