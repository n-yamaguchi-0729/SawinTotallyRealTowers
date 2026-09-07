import SawinTotallyRealTowers.QuadraticClosureClassification
import SawinTotallyRealTowers.QuadraticCompositum
import SawinTotallyRealTowers.SixPrimeQuadraticCompositum
import SawinTotallyRealTowers.SixPrimeSquareClasses

set_option autoImplicit false

/-!
# Exhausting the quadratic layers of the six-prime real tower

The ramification and discriminant classification supplies a positive
squarefree radicand for every quadratic layer. Its explicit square-class
factorization then places that layer inside the compositum of the five
chosen quadratic fields.
-/

open scoped NumberField BigOperators
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

private theorem sawinQuadraticRoot_mem_compositum (i : Fin 5) :
    quadraticClosureRoot (sawinQuadraticRadicand i : ℚ) ∈
      sawinQuadraticCompositum.toIntermediateField := by
  apply sawinQuadraticLayer_le_compositum i
  exact IntermediateField.mem_adjoin_simple_self ℚ
    (quadraticClosureRoot (sawinQuadraticRadicand i : ℚ))

/-- Every quadratic layer of the real tower unramified outside the six
specified primes lies in the concrete five-generator compositum. -/
theorem admissible_quadratic_le_sawinQuadraticCompositum
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hDegree : Module.finrank ℚ E = 2)
    (hE : IsAdmissibleFiniteLayer 2 sawinRationalPrimeSupport E) :
    E ≤ sawinQuadraticCompositum := by
  obtain ⟨d, hd, hdPos, hdSquarefree, hMod, hSupport, hField⟩ :=
    exists_supported_radicand_of_admissible_quadratic E hDegree
      sawinRationalPrimeSupport hE two_not_mem_sawinRationalPrimeSupport
  have hPrimeSupport : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d →
      p ∈ ({3, 5, 7, 11, 13, 17} : Finset ℕ) := by
    intro p hp hDiv
    exact (rationalPrime_mem_sawinRationalPrimeSupport_iff
      (⟨p, hp⟩ : Nat.Primes)).mp (hSupport ⟨p, hp⟩ hDiv)
  obtain ⟨s, hs, q, _hq, hClass⟩ :=
    exists_five_generator_squareClass_of_int_support
      d hdPos.le hdSquarefree hPrimeSupport hMod
  rw [hField]
  apply IntermediateField.adjoin_simple_le_iff.mpr
  apply squareRoot_mem_of_squareClass_product
    sawinQuadraticCompositum.toIntermediateField s
    (fun r : ℕ ↦ (r : ℚ)) (fun r : ℕ ↦ quadraticClosureRoot (r : ℚ))
    (d : ℚ) q (quadraticClosureRoot (d : ℚ))
    (quadraticClosureRoot_sq (d : ℚ))
    (fun r _ ↦ quadraticClosureRoot_sq (r : ℚ)) ?_ hClass
  intro r hr
  have hrFive := hs hr
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrFive
  rcases hrFive with rfl | rfl | rfl | rfl | rfl
  · exact sawinQuadraticRoot_mem_compositum 0
  · exact sawinQuadraticRoot_mem_compositum 1
  · exact sawinQuadraticRoot_mem_compositum 2
  · exact sawinQuadraticRoot_mem_compositum 3
  · exact sawinQuadraticRoot_mem_compositum 4

/-- The five-generator compositum is exactly the compositum of all
admissible quadratic subfields, rather than only a subfield of that tower. -/
theorem sawinQuadraticCompositum_eq_iSup_quadratic_layers :
    sawinQuadraticCompositum.toIntermediateField =
      ⨆ (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
        (_ : IsAdmissibleFiniteLayer 2 sawinRationalPrimeSupport E)
        (_ : Module.finrank ℚ E = 2), E.toIntermediateField := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    ⨆ (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
      (_ : IsAdmissibleFiniteLayer 2 sawinRationalPrimeSupport E)
      (_ : Module.finrank ℚ E = 2), E.toIntermediateField
  change sawinQuadraticCompositum.toIntermediateField = M
  apply le_antisymm
  · have hLayer : ∀ i : Fin 5, (sawinQuadraticLayer i).toIntermediateField ≤ M := by
      intro i
      exact le_iSup_of_le (sawinQuadraticLayer i)
        (le_iSup_of_le (isAdmissibleFiniteLayer_sawinQuadraticLayer i)
          (le_iSup_of_le (quadraticClosure_finrank
            (sawinQuadraticRadicand i : ℚ) (sawinQuadraticRadicand_nonsquare i)) le_rfl))
    exact Finset.sup_induction
      (p := fun E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) ↦
        E.toIntermediateField ≤ M)
      bot_le
      (fun E hE F hF ↦
        (show E.toIntermediateField ⊔ F.toIntermediateField ≤ M from sup_le hE hF))
      (fun i _hi ↦ hLayer i)
  · exact iSup_le fun E ↦ iSup_le fun hE ↦ iSup_le fun hDegree ↦
      admissible_quadratic_le_sawinQuadraticCompositum E hDegree hE

end ClassFieldTower.Sawin
