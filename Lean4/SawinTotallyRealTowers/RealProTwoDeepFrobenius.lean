import SawinTotallyRealTowers.RealProPFrobeniusStage
import SawinTotallyRealTowers.RealProPFrobenius
import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.SixPrimeSupport
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitPrimesModFour
import ProCGroups.ProP.Zassenhaus.Depth
import ProCGroups.FiniteGeneration.Basic
import Mathlib.Data.Finset.Union
import Mathlib.NumberTheory.NumberField.Basic

set_option autoImplicit false

/-!
# New rational primes with deep Frobenius lifts

The actual finite stage detecting source depth has completely split rational
primes congruent to one modulo four outside any finite set. Excluding also
the six allowed ramified primes gives an actual new unramified Frobenius
with a source lift of the prescribed depth.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open ClassFieldTower.ProP ProCGroups.FiniteGeneration
open AlgebraicNumberTheory.PrimeSelection

universe u

private local instance deepFrobeniusPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- Outside any finite set and the six ramified primes, a rational prime
congruent to one modulo four has an actual Frobenius lift of any requested
depth in the given finitely generated profinite source. -/
theorem exists_sawinPrime_with_deep_frobenius_lift
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (hfg : TopologicallyFinitelyGenerated F)
    (q : F →ₜ* (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
      maximalRealProPOutside 2 sawinRationalPrimeSupport))
    (hq : Function.Surjective q) (n : ℕ) (bad : Finset ℕ) :
    ∃ ℓ : Nat.Primes, ℓ.val ∉ bad ∧
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ℓ ∉ sawinRationalPrimeSupport ∧
      ℓ.val % 4 = 1 ∧
      ∃ f : F, q f = maximalRealProPArithmeticFrobenius 2 sawinRationalPrimeSupport
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ℓ) ∧
        ZassenhausDepthAtLeast 2 n f := by
  obtain ⟨U, hU⟩ := exists_realProPOpenNormalStage_with_deep_frobenius_lifts
    2 sawinRationalPrimeSupport hfg q hq n
  let M : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
    (realProPOpenNormalStage 2 sawinRationalPrimeSupport U).val
  let : NumberField M := NumberField.of_module_finite ℚ M
  let : IsGalois ℚ M.toIntermediateField := M.isGalois
  obtain ⟨ℓ, hbad, hmod, hsplit⟩ :=
    exists_completelySplitPrime_modFour_one_not_mem M (bad ∪ sawinRationalPrimes)
  have hbad₀ : ℓ.val ∉ bad := fun h ↦ hbad (Finset.mem_union_left _ h)
  have hsupport :
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ℓ ∉ sawinRationalPrimeSupport := by
    intro h
    exact hbad (Finset.mem_union_right _
      ((rationalPrime_mem_sawinRationalPrimeSupport_iff ℓ).mp h))
  exact ⟨ℓ, hbad₀, hsupport, hmod,
    hU ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ℓ) hsplit⟩

end ClassFieldTower.Sawin
