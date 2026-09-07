import SawinTotallyRealTowers.RealProTwoInitialGroup
import SawinTotallyRealTowers.RealProTwoGeneratorRank
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.SixPrimeSupport
import ProCGroups.ProP.Presentation.RelationCardinal
import ProCGroups.ProP.Presentation.GeneratorRank
import ProCGroups.ProP.Presentation.FiniteGeneration
import Mathlib.FieldTheory.Galois.Profinite

set_option autoImplicit false

/-!
# A five-generator minimal presentation of the actual initial group

Choose a presentation attaining the least relation count constructed in S1.
Minimality identifies its displayed generator count with the actual rank five.
The same presentation, including its free source and relators, is retained.
-/

namespace ClassFieldTower.Sawin

open ProCGroups ClassFieldTower.ProP

private local instance initialPresentationPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private local instance initialPresentationIsGalois :
    IsGalois ℚ (maximalRealProPOutside 2 sawinRationalPrimeSupport) :=
  maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport

/-- The initial arithmetic group has an actual minimal presentation on five
generators and at most six relators. The chosen relator count attains the
least relation rank supplied by S1. -/
theorem exists_sawinInitialProTwo_minimalPresentation :
    ∃ sourceData : FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{0, 0}
      (FiniteGroupClass.pGroup 2),
      ∃ r : ℕ, ∃ P : FiniteProPPresentation 2 5 r sourceData
        (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
          maximalRealProPOutside 2 sawinRationalPrimeSupport),
        P.IsMinimal ∧ r ≤ 6 := by
  obtain ⟨hG, hr, _, _⟩ := sawinInitialProTwoGroup_structure.2.2.2
  obtain ⟨sourceData, d, P, hP⟩ := exists_presentation_relationCard_eq_minimal hG
  have hd : d = 5 :=
    (P.target_topologicalGeneratorRank_eq hP).symm.trans maximalRealProTwo_generatorRank.2
  subst d
  exact ⟨sourceData, _, P, hP, hr⟩

end ClassFieldTower.Sawin
