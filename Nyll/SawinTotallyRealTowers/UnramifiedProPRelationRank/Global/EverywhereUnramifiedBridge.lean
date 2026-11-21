/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsEverywhereUnramified
public import Nyll.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsUnramifiedAtFinitePlaces
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.MathlibUnramifiedInterface
public import Mathlib.RingTheory.Etale.Basic

/-!
# Everywhere-unramified bridges for number fields

This file combines the finite-prime bridges for rings of integers with the
infinite-place API. It also transports everywhere-unramifiedness across an
equivalence of top fields and supplies odd-degree Galois constructors.
-/

@[expose] public section

open ClassFieldTheory

open scoped NumberField

noncomputable section

universe u v w

namespace ClassFieldTower.Martinet

/-- Finite-prime and infinite-place unramifiedness together give
everywhere-unramifiedness. -/
theorem everywhereUnramified_of_finitePlaces_of_infinitePlaces
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    (hFinite : IsUnramifiedAtFinitePlaces K L)
    (hInfinite : IsUnramifiedAtInfinitePlaces K L) :
    IsEverywhereUnramified K L :=
  ⟨hFinite, hInfinite⟩

/-- The finite-place predicate is equivalent to the ramification-index-one
formula used by the benchmark. -/
theorem isUnramifiedAtFinitePlaces_iff_ramificationIdx_eq_one
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] :
    IsUnramifiedAtFinitePlaces K L ↔
      ∀ (p : Ideal (𝓞 K)) (P : Ideal (𝓞 L)),
        p.IsPrime → p ≠ ⊥ → P ∈ p.primesOver (𝓞 L) →
          P.ramificationIdx (𝓞 K) = 1 := by
  constructor
  · intro h p P _ hp hP
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 L) :=
      { asIdeal := P
        isPrime := hP.1
        ne_bot := Ideal.ne_bot_of_mem_primesOver hp hP }
    let _ : P.IsPrime := hP.1
    let _ : Algebra.IsUnramifiedAt (𝓞 K) P := h.atPrime v
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  · intro h
    apply (IsUnramifiedAtFinitePlaces.iff_forall_above K L).2
    intro P
    have hBase : P.asIdeal.under (𝓞 K) ≠ ⊥ := by
      simpa only [finitePlaceBelow_asIdeal] using
        (finitePlaceBelow (K := K) P).ne_bot
    let _ : Finite ((𝓞 K) ⧸ P.asIdeal.under (𝓞 K)) :=
      Ring.HasFiniteQuotients.finiteQuotient hBase
    let _ : PerfectField (P.asIdeal.under (𝓞 K)).ResidueField :=
      PerfectField.ofFinite
    rw [← Ideal.ramificationIdx_eq_one_iff]
    exact h (P.asIdeal.under (𝓞 K)) P.asIdeal inferInstance hBase
      ⟨P.isPrime, ⟨rfl⟩⟩

/-- Infinite-place unramifiedness is exactly the assertion that every lift of
a real place is real. -/
theorem isUnramifiedAtInfinitePlaces_iff_real_lifts
    {K : Type u} {L : Type v}
    [Field K] [Field L] [Algebra K L] :
    IsUnramifiedAtInfinitePlaces K L ↔
      ∀ w : NumberField.InfinitePlace K, w.IsReal →
        ∀ w' : NumberField.InfinitePlace L,
          w'.comap (algebraMap K L) = w → w'.IsReal := by
  constructor
  · intro h w hw w' hw'
    rcases NumberField.InfinitePlace.isUnramified_iff.mp
        (h.isUnramified w') with hwReal | hBaseComplex
    · exact hwReal
    · have : w.IsComplex := by
        simpa only [hw'] using hBaseComplex
      exact ((NumberField.InfinitePlace.not_isComplex_iff_isReal.mpr hw) this).elim
  · intro h
    refine ⟨fun w' ↦ ?_⟩
    rw [NumberField.InfinitePlace.isUnramified_iff]
    by_cases hw : (w'.comap (algebraMap K L)).IsReal
    · exact Or.inl (h _ hw w' rfl)
    · exact Or.inr
        (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw)

/-- Formal unramifiedness of the rings of integers, together with the
infinite-place condition, gives everywhere-unramifiedness. -/
theorem everywhereUnramified_of_formallyUnramified
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [Algebra.FormallyUnramified (𝓞 K) (𝓞 L)]
    (hInfinite : IsUnramifiedAtInfinitePlaces K L) :
    IsEverywhereUnramified K L :=
  everywhereUnramified_of_finitePlaces_of_infinitePlaces
    inferInstance hInfinite

/-- Étaleness of the rings of integers, together with the infinite-place
condition, gives everywhere-unramifiedness. -/
theorem everywhereUnramified_of_etale
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L]
    [Algebra.Etale (𝓞 K) (𝓞 L)]
    (hInfinite : IsUnramifiedAtInfinitePlaces K L) :
    IsEverywhereUnramified K L :=
  everywhereUnramified_of_finitePlaces_of_infinitePlaces
    inferInstance hInfinite

/-- An odd-degree Galois extension that is unramified at finite places is
everywhere unramified. -/
theorem everywhereUnramified_of_finitePlaces_of_odd_finrank
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    (hFinite : IsUnramifiedAtFinitePlaces K L)
    (hOdd : Odd (Module.finrank K L)) :
    IsEverywhereUnramified K L :=
  everywhereUnramified_of_finitePlaces_of_infinitePlaces hFinite
    (IsUnramifiedAtInfinitePlaces_of_odd_finrank hOdd)

/-- A formally unramified ring-of-integers extension of odd Galois degree is
everywhere unramified. -/
theorem everywhereUnramified_of_formallyUnramified_of_odd_finrank
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [Algebra.FormallyUnramified (𝓞 K) (𝓞 L)]
    (hOdd : Odd (Module.finrank K L)) :
    IsEverywhereUnramified K L :=
  everywhereUnramified_of_finitePlaces_of_odd_finrank
    inferInstance hOdd

/-- An étale ring-of-integers extension of odd Galois degree is everywhere
unramified. -/
theorem everywhereUnramified_of_etale_of_odd_finrank
    {K : Type u} {L : Type v}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]
    [Algebra.Etale (𝓞 K) (𝓞 L)]
    (hOdd : Odd (Module.finrank K L)) :
    IsEverywhereUnramified K L :=
  everywhereUnramified_of_finitePlaces_of_odd_finrank
    inferInstance hOdd

/-- The library predicate is equivalent to the benchmark's explicit finite-
and infinite-place clauses. -/
theorem isEverywhereUnramified_iff_explicit
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
      ⟨isUnramifiedAtFinitePlaces_iff_ramificationIdx_eq_one.mp
          h.1,
        isUnramifiedAtInfinitePlaces_iff_real_lifts.mp
          h.2⟩
  · rintro ⟨hFinite, hInfinite⟩
    exact everywhereUnramified_of_finitePlaces_of_infinitePlaces
      (isUnramifiedAtFinitePlaces_iff_ramificationIdx_eq_one.mpr hFinite)
      (isUnramifiedAtInfinitePlaces_iff_real_lifts.mpr hInfinite)

end ClassFieldTower.Martinet
