import SawinTotallyRealTowers.FiveQuadraticSquareClasses
import SawinTotallyRealTowers.QuadraticAdmissibleLayer
import SawinTotallyRealTowers.SixPrimeSupport
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# The five quadratic layers over the six-prime support

The radicands `5, 13, 17, 21, 33` give actual finite Galois fields inside
the chosen algebraic closure of ℚ. Each satisfies the prescribed finite
ramification and real-place conditions. Their finite supremum is therefore
an admissible compositum of these five quadratic fields.
-/

open scoped NumberField
open IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

private theorem sawinQuadraticRadicand_arithmetic (i : Fin 5) :
    0 < (sawinQuadraticRadicand i : ℤ) ∧
      Squarefree (sawinQuadraticRadicand i : ℤ).natAbs ∧
      (sawinQuadraticRadicand i : ℤ) % 4 = 1 ∧
      (sawinQuadraticRadicand i).primeFactors ⊆ sawinRationalPrimes := by
  fin_cases i <;> decide +kernel

/-- The quadratic field associated to the indexed radicand. -/
def sawinQuadraticLayer (i : Fin 5) :
    FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  quadraticClosure (sawinQuadraticRadicand i : ℚ) (sawinQuadraticRadicand_nonsquare i)

/-- Each of the five constructed quadratic fields is an admissible real
two-extension with ramification restricted to the six allowed primes. -/
theorem isAdmissibleFiniteLayer_sawinQuadraticLayer (i : Fin 5) :
    IsAdmissibleFiniteLayer 2 sawinRationalPrimeSupport (sawinQuadraticLayer i) := by
  have hArithmetic := sawinQuadraticRadicand_arithmetic i
  have hNonzero : sawinQuadraticRadicand i ≠ 0 := by
    intro hZero
    have hPos := hArithmetic.1
    rw [hZero] at hPos
    exact (lt_irrefl (0 : ℤ)) hPos
  have hNonsquare : ¬ IsSquare ((sawinQuadraticRadicand i : ℤ) : ℚ) := by
    simpa only [Int.cast_natCast] using sawinQuadraticRadicand_nonsquare i
  have hSupport : ∀ q : Nat.Primes, (q : ℤ) ∣ (sawinQuadraticRadicand i : ℤ) →
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ∈
        sawinRationalPrimeSupport := by
    intro q hDiv
    apply (rationalPrime_mem_sawinRationalPrimeSupport_iff q).mpr
    apply hArithmetic.2.2.2
    exact Nat.mem_primeFactors.mpr ⟨q.property, Int.ofNat_dvd.mp hDiv, hNonzero⟩
  simpa only [sawinQuadraticLayer, Int.cast_natCast] using
    isAdmissibleFiniteLayer_quadraticClosure (sawinQuadraticRadicand i : ℤ)
      hArithmetic.1 hArithmetic.2.1 hArithmetic.2.2.1 hNonsquare
      sawinRationalPrimeSupport hSupport

/-- The actual finite compositum of the five quadratic layers. -/
def sawinQuadraticCompositum : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) :=
  Finset.univ.sup sawinQuadraticLayer

/-- Each chosen quadratic field is contained in their finite compositum. -/
theorem sawinQuadraticLayer_le_compositum (i : Fin 5) :
    sawinQuadraticLayer i ≤ sawinQuadraticCompositum :=
  Finset.le_sup (f := sawinQuadraticLayer) (Finset.mem_univ i)

/-- The compositum remains an admissible finite layer by the proved
compositum closure of the arithmetic conditions. -/
theorem isAdmissibleFiniteLayer_sawinQuadraticCompositum :
    IsAdmissibleFiniteLayer 2 sawinRationalPrimeSupport sawinQuadraticCompositum := by
  exact Finset.sup_induction
    (isAdmissibleFiniteLayer_bot 2 sawinRationalPrimeSupport)
    (fun E hE F hF ↦ IsAdmissibleFiniteLayer.sup hE hF)
    (fun i _hi ↦ isAdmissibleFiniteLayer_sawinQuadraticLayer i)

end ClassFieldTower.Sawin
