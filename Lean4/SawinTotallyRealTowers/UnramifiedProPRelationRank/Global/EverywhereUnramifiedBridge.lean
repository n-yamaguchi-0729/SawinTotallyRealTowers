import ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.FiniteUnramifiedEtaleBridge

set_option autoImplicit false
/-!
# Everywhere-unramified bridges for number fields

This file combines the finite-prime bridges for rings of integers with the
infinite-place API. It also transports everywhere-unramifiedness across an
equivalence of top fields and supplies odd-degree Galois constructors.
-/

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
    IsEverywhereUnramified K L where
  finitePlaces := hFinite
  infinitePlaces := hInfinite

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
    let _ : Algebra.IsUnramifiedAt (𝓞 K) P := h v
    exact Ideal.ramificationIdx_eq_one P (𝓞 K)
  · intro h P
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

/-- Infinite-place unramifiedness is preserved by an algebra equivalence of
the top field. -/
theorem infinitePlaceUnramifiedness_map_algEquiv
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M)
    (h : IsUnramifiedAtInfinitePlaces K L) :
    IsUnramifiedAtInfinitePlaces K M := by
  rw [isUnramifiedAtInfinitePlaces_iff_real_lifts] at h ⊢
  intro w hw wM hwM
  have hComap :
      (wM.comap (e : L →+* M)).comap (algebraMap K L) = w := by
    rw [← NumberField.InfinitePlace.comap_comp]
    calc
      wM.comap ((e : L →+* M).comp (algebraMap K L)) =
          wM.comap (algebraMap K M) := by
        congr 1
        ext x
        exact e.commutes x
      _ = w := hwM
  have hReal : (wM.comap (e : L →+* M)).IsReal :=
    h w hw _ hComap
  exact (NumberField.InfinitePlace.isReal_comap_iff e.toRingEquiv).mp hReal

/-- Everywhere-unramifiedness is preserved when the top number field is
replaced by an equivalent algebra over the base field. -/
theorem everywhereUnramified_congrTop
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M)
    (h : IsEverywhereUnramified K L) :
    IsEverywhereUnramified K M :=
  everywhereUnramified_of_finitePlaces_of_infinitePlaces
    (finitePlaceUnramifiedness_congrTop e h.finitePlaces)
    (infinitePlaceUnramifiedness_map_algEquiv e h.infinitePlaces)

/-- Everywhere-unramifiedness is invariant under an algebra equivalence of
the top number field. -/
theorem isEverywhereUnramified_congrTop
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Field M] [NumberField M]
    [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) :
    IsEverywhereUnramified K L ↔ IsEverywhereUnramified K M :=
  ⟨everywhereUnramified_congrTop e,
    everywhereUnramified_congrTop e.symm⟩

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
    finitePlaceUnramifiedness_of_formallyUnramified hInfinite

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
    finitePlaceUnramifiedness_of_etale hInfinite

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
    finitePlaceUnramifiedness_of_formallyUnramified hOdd

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
    finitePlaceUnramifiedness_of_etale hOdd

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
          h.finitePlaces,
        isUnramifiedAtInfinitePlaces_iff_real_lifts.mp
          h.infinitePlaces⟩
  · rintro ⟨hFinite, hInfinite⟩
    exact everywhereUnramified_of_finitePlaces_of_infinitePlaces
      (isUnramifiedAtFinitePlaces_iff_ramificationIdx_eq_one.mpr hFinite)
      (isUnramifiedAtInfinitePlaces_iff_real_lifts.mpr hInfinite)

end ClassFieldTower.Martinet
