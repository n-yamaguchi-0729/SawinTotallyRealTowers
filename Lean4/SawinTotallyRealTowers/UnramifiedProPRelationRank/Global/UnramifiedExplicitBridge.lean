/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedEtaleBridge
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedBridge
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Locus

set_option autoImplicit false
/-!
# Explicit everywhere-unramified benchmark bridge

This file packages the library predicates for finite and infinite
unramifiedness in the exact explicit form used by the Shafarevich benchmark.
It also connects finite-place unramifiedness to formal unramifiedness and to
finite étale algebras of rings of integers.
-/

open scoped NumberField

noncomputable section

universe u v

namespace ClassFieldTower.Martinet

/-- Finite-place unramifiedness in the exact ramification-index form used by
the benchmark contract. -/
theorem finitePlaceUnramifiedness_iff_explicitRamificationIdx
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] :
    IsUnramifiedAtFinitePlaces K L ↔
      ∀ (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)),
        p.IsPrime → p ≠ ⊥ → P ∈ p.primesOver (𝓞 L) →
          P.ramificationIdx (𝓞 K) = 1 :=
  isUnramifiedAtFinitePlaces_iff_ramificationIdx_eq_one

/-- Unramifiedness at every finite place is equivalent to formal
unramifiedness of the corresponding extension of rings of integers. -/
theorem finitePlaceUnramifiedness_iff_formallyUnramified
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] :
    IsUnramifiedAtFinitePlaces K L ↔
      Algebra.FormallyUnramified (𝓞 K) (𝓞 L) := by
  constructor
  · intro h
    rw [Algebra.formallyUnramified_iff_forall]
    intro P
    by_cases hP : P.asIdeal = ⊥
    · simpa only [hP] using
        (Algebra.isUnramifiedAt_bot (R := 𝓞 K) (S := 𝓞 L))
    · exact h
        { asIdeal := P.asIdeal
          isPrime := P.isPrime
          ne_bot := hP }
  · intro h
    let hFormal : Algebra.FormallyUnramified (𝓞 K) (𝓞 L) := h
    let _ := hFormal
    exact finitePlaceUnramifiedness_of_formallyUnramified

/-- Finite-place unramifiedness makes the extension of rings of integers
étale. -/
theorem finitePlaceUnramifiedness_to_etale
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    (h : IsUnramifiedAtFinitePlaces K L) :
    Algebra.Etale (𝓞 K) (𝓞 L) := by
  let hFinite : Module.Finite (𝓞 K) (𝓞 L) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
  let _ := hFinite
  let hModulePresentation : Module.FinitePresentation (𝓞 K) (𝓞 L) :=
    Module.finitePresentation_of_finite (𝓞 K) (𝓞 L)
  let _ := hModulePresentation
  let hAlgebraPresentation : Algebra.FinitePresentation (𝓞 K) (𝓞 L) :=
    inferInstance
  let _ := hAlgebraPresentation
  let hFormal : Algebra.FormallyUnramified (𝓞 K) (𝓞 L) :=
    finitePlaceUnramifiedness_iff_formallyUnramified.mp h
  let _ := hFormal
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- The finite étale algebra of rings of integers attached to a
finite-place-unramified number-field extension. -/
def finitePlaceUnramifiedness_toFiniteEtale
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    (h : IsUnramifiedAtFinitePlaces K L) :
    CommAlgCat.FiniteEtale (𝓞 K) := by
  letI hFinite : Module.Finite (𝓞 K) (𝓞 L) :=
    HilbertRamification.Dedekind.ringOfIntegers_moduleFinite
  letI hEtale : Algebra.Etale (𝓞 K) (𝓞 L) :=
    finitePlaceUnramifiedness_to_etale h
  exact CommAlgCat.FiniteEtale.of (𝓞 K) (𝓞 L)

/-- Infinite-place unramifiedness in the exact real-place lifting form used
by the benchmark contract. -/
theorem infinitePlaceUnramifiedness_iff_explicitRealLifts
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] :
    IsUnramifiedAtInfinitePlaces K L ↔
      ∀ w : NumberField.InfinitePlace K, w.IsReal →
        ∀ w' : NumberField.InfinitePlace L,
          w'.comap (algebraMap K L) = w → w'.IsReal :=
  isUnramifiedAtInfinitePlaces_iff_real_lifts

/-- The existing everywhere-unramified predicate is exactly the conjunction
of the finite and infinite clauses in the benchmark contract. -/
theorem everywhereUnramified_iff_explicitClauses
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] :
    IsEverywhereUnramified K L ↔
      (∀ (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)),
          p.IsPrime → p ≠ ⊥ → P ∈ p.primesOver (𝓞 L) →
            P.ramificationIdx (𝓞 K) = 1) ∧
        (∀ w : NumberField.InfinitePlace K, w.IsReal →
          ∀ w' : NumberField.InfinitePlace L,
            w'.comap (algebraMap K L) = w → w'.IsReal) := by
  constructor
  · intro h
    exact
      ⟨finitePlaceUnramifiedness_iff_explicitRamificationIdx.mp
          h.finitePlaces,
        infinitePlaceUnramifiedness_iff_explicitRealLifts.mp
          h.infinitePlaces⟩
  · rintro ⟨hFinite, hInfinite⟩
    exact everywhereUnramified_of_finitePlaces_of_infinitePlaces
      (finitePlaceUnramifiedness_iff_explicitRamificationIdx.mpr hFinite)
      (infinitePlaceUnramifiedness_iff_explicitRealLifts.mpr hInfinite)

end ClassFieldTower.Martinet
