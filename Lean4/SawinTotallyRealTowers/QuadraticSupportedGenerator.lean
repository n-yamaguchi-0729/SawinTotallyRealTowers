import SawinTotallyRealTowers.QuadraticFieldDiscriminant
import SawinTotallyRealTowers.QuadraticReality
import SawinTotallyRealTowers.QuadraticSquarefreeGenerator
import SawinTotallyRealTowers.RationalRamificationSupport
import Mathlib.Algebra.Order.Ring.Cast

set_option autoImplicit false

/-!
# Positive squarefree generators with prescribed ramification support

A totally real quadratic number field has a positive squarefree integer
radicand. If its allowed finite ramification support excludes two, the
discriminant formula forces the radicand to be one modulo four. The
discriminant is then the radicand itself, so every prime divisor belongs
to the prescribed support.
-/

open scoped NumberField
open NumberField IsDedekindDomain

universe u

namespace ClassFieldTower.Sawin

/-- A totally real quadratic number field unramified outside a support
excluding two has a positive squarefree radicand congruent to one modulo
four, all of whose prime divisors lie in that support. -/
theorem exists_positive_squarefree_supported_generator
    (L : Type u) [Field L] [NumberField L]
    [Algebra.IsQuadraticExtension ℚ L] [IsTotallyReal L]
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hOutside : IsUnramifiedAtFinitePlacesOutside ℚ L T)
    (hTwo : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉ T) :
    ∃ d : ℤ, ∃ β : L,
      0 < d ∧ Squarefree d.natAbs ∧ d % 4 = 1 ∧
        β ^ 2 = algebraMap ℚ L (d : ℚ) ∧
        IntermediateField.adjoin ℚ ({β} : Set L) = ⊤ ∧
        ¬ IsSquare (d : ℚ) ∧
        ∀ q : Nat.Primes, (q : ℤ) ∣ d →
          (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ∈ T := by
  obtain ⟨d, β, hdSquarefree, hdNe, hSquare, hGenerate, hNonsquare⟩ :=
    exists_squarefree_int_generator_of_isQuadraticExtension L
  have hdNonneg : 0 ≤ d :=
    Int.cast_nonneg_iff.mp (rat_nonneg_of_sq_of_isTotallyReal L hSquare)
  have hdPos : 0 < d := lt_of_le_of_ne hdNonneg hdNe.symm
  have hDiscrSupport :=
    (isUnramifiedAtFinitePlacesOutside_rat_iff_discr L T).mp hOutside
  have hMod : d % 4 = 1 := by
    by_contra hMod
    apply hTwo
    apply hDiscrSupport (⟨2, Nat.prime_two⟩ : Nat.Primes)
    change (2 : ℤ) ∣ NumberField.discr L
    rw [numberField_discr_of_mod_four_ne_one L d hdSquarefree β hSquare hGenerate hMod]
    exact dvd_mul_of_dvd_left (by decide : (2 : ℤ) ∣ 4) d
  refine ⟨d, β, hdPos, hdSquarefree, hMod, hSquare, hGenerate, hNonsquare, ?_⟩
  intro q hDiv
  apply hDiscrSupport q
  rw [numberField_discr_of_mod_four_eq_one L d hdSquarefree β hSquare hGenerate hMod]
  exact hDiv

end ClassFieldTower.Sawin
