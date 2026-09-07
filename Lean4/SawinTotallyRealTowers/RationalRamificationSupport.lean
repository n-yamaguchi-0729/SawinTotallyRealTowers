import SawinTotallyRealTowers.RamificationSupport
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Unramified.Locus

set_option autoImplicit false

/-!
# Rational primes in the finite ramification support

The canonical identification of the integers of ℚ with ℤ identifies their
local unramifiedness conditions. Under the equivalence between finite places
of ℚ and positive rational primes, the allowed ramification support therefore
contains exactly the prime divisors required by the absolute discriminant.
-/

open scoped NumberField
open NumberField IsDedekindDomain

universe u

namespace ClassFieldTower.Sawin

/-- The local unramifiedness conditions over the integers of ℚ and over ℤ
agree. The canonical integer map onto `𝓞 ℚ` is surjective. -/
theorem isUnramifiedAt_rat_iff_int
    (L : Type u) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    Algebra.IsUnramifiedAt (𝓞 ℚ) P ↔ Algebra.IsUnramifiedAt ℤ P := by
  constructor
  · intro h
    let : Algebra.IsUnramifiedAt (𝓞 ℚ) P := h
    let : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
      Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (𝓞 ℚ))
        (Rat.int_algebraMap_surjective (𝓞 ℚ))
    exact Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime P)
  · intro h
    let : Algebra.IsUnramifiedAt ℤ P := h
    exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ P

private theorem rationalPrime_asIdeal (q : Nat.Primes) :
    ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q).asIdeal =
      Ideal.span {(q : 𝓞 ℚ)} := by
  change (Ideal.span {(q : ℤ)}).map
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom = _
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_natCast]

private theorem finitePlaceBelow_eq_rationalPrime_iff
    (L : Type u) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (q : Nat.Primes) :
    finitePlaceBelow (K := ℚ) P =
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ↔
        (q : 𝓞 L) ∈ P.asIdeal := by
  have hMem : (q : 𝓞 ℚ) ∈ (finitePlaceBelow (K := ℚ) P).asIdeal ↔
      (q : 𝓞 L) ∈ P.asIdeal := by
    change algebraMap (𝓞 ℚ) (𝓞 L) (q : 𝓞 ℚ) ∈ P.asIdeal ↔ _
    rw [map_natCast]
  constructor
  · intro h
    apply hMem.mp
    rw [h, rationalPrime_asIdeal]
    exact Ideal.mem_span_singleton_self (q : 𝓞 ℚ)
  · intro h
    apply HeightOneSpectrum.ext
    apply Eq.symm
    apply (((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q).isPrime.isMaximal
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q).ne_bot).eq_of_le
      (finitePlaceBelow (K := ℚ) P).isPrime.ne_top
    rw [rationalPrime_asIdeal]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr (hMem.mpr h))

private theorem not_dvd_discr_iff_finitePlaceBelow
    (L : Type u) [Field L] [NumberField L] (q : Nat.Primes) :
    ¬ (q : ℤ) ∣ NumberField.discr L ↔
      ∀ P : HeightOneSpectrum (𝓞 L),
        finitePlaceBelow (K := ℚ) P =
          (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q →
            Algebra.IsUnramifiedAt (𝓞 ℚ) P.asIdeal := by
  rw [NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L)
    (Nat.prime_iff_prime_int.mp q.property)]
  constructor
  · intro h P hBelow
    apply (isUnramifiedAt_rat_iff_int L P.asIdeal).mpr
    apply h P.asIdeal P.isPrime
    simpa only [Int.cast_natCast] using
      (finitePlaceBelow_eq_rationalPrime_iff L P q).mp hBelow
  · intro h P hP hMem
    simp only [Int.cast_natCast] at hMem
    let : P.IsPrime := hP
    have hNe : P ≠ ⊥ := by
      intro hBot
      have hZero : (q : 𝓞 L) = 0 := by
        simpa only [hBot, Ideal.mem_bot] using hMem
      exact (Nat.cast_ne_zero.mpr q.property.ne_zero) hZero
    let Q : HeightOneSpectrum (𝓞 L) :=
      { asIdeal := P
        isPrime := hP
        ne_bot := hNe }
    apply (isUnramifiedAt_rat_iff_int L P).mp
    exact h Q ((finitePlaceBelow_eq_rationalPrime_iff L Q q).mpr hMem)

/-- A number field is unramified outside the prescribed rational finite
places exactly when that set contains every prime divisor of its absolute
discriminant. No normality or degree restriction is needed. -/
theorem isUnramifiedAtFinitePlacesOutside_rat_iff_discr
    (L : Type u) [Field L] [NumberField L]
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IsUnramifiedAtFinitePlacesOutside ℚ L T ↔
      ∀ q : Nat.Primes, (q : ℤ) ∣ NumberField.discr L →
        (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ∈ T := by
  constructor
  · intro h q hDiv
    by_contra hOutside
    apply ((not_dvd_discr_iff_finitePlaceBelow L q).mpr ?_) hDiv
    intro P hBelow
    apply h P
    rw [hBelow]
    exact hOutside
  · intro h P hOutside
    let q : Nat.Primes :=
      Rat.HeightOneSpectrum.primesEquiv (finitePlaceBelow (K := ℚ) P)
    have hBelow : finitePlaceBelow (K := ℚ) P =
        (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q :=
      ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm_apply_apply
        (finitePlaceBelow (K := ℚ) P)).symm
    have hNotDiv : ¬ (q : ℤ) ∣ NumberField.discr L := by
      intro hDiv
      apply hOutside
      rw [hBelow]
      exact h q hDiv
    exact (not_dvd_discr_iff_finitePlaceBelow L q).mp hNotDiv P hBelow

end ClassFieldTower.Sawin
