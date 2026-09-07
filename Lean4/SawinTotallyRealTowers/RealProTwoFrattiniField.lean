import SawinTotallyRealTowers.FixedFieldIntersection
import SawinTotallyRealTowers.ProTwoFrattini
import SawinTotallyRealTowers.RealProTwoQuadraticFixedFields
import SawinTotallyRealTowers.MaximalRealProPGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# The Frattini fixed field of the initial real pro-two group

The group-theoretic intersection over quadratic quotients and the
arithmetic classification of all quadratic layers identify the actual
Frattini fixed field. No finite-generation hypothesis is used.
-/

namespace ClassFieldTower.Sawin

/-- The Frattini fixed field, lifted to the fixed algebraic closure, is
exactly the constructed five-generator multiquadratic field. -/
theorem maximalRealProTwo_frattini_fixedField :
    IntermediateField.lift (IntermediateField.fixedField
      (ClassFieldTower.ProP.profiniteFrattini
        (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
          maximalRealProPOutside 2 sawinRationalPrimeSupport))) =
      sawinQuadraticCompositum.toIntermediateField := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    maximalRealProPOutside 2 sawinRationalPrimeSupport
  let : IsGalois ℚ M := maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Type := {U : OpenNormalSubgroup (M ≃ₐ[ℚ] M) //
    (U : Subgroup (M ≃ₐ[ℚ] M)).index = 2}
  have hFrattini : ClassFieldTower.ProP.profiniteFrattini (M ≃ₐ[ℚ] M) =
      ⨅ U : I, (U.val : Subgroup (M ≃ₐ[ℚ] M)) :=
    (profiniteFrattini_eq_iInf_openNormal_index_two (M ≃ₐ[ℚ] M)
      (maximalRealProPOutside_galoisGroup_hasPGroupOpenNormalBasis
        2 sawinRationalPrimeSupport)).trans iInf_subtype'
  have hFixed : IntermediateField.fixedField
      (ClassFieldTower.ProP.profiniteFrattini (M ≃ₐ[ℚ] M)) =
        ⨆ U : I, IntermediateField.fixedField (U.val : Subgroup (M ≃ₐ[ℚ] M)) := by
    rw [hFrattini]
    exact fixedField_iInf_eq_iSup_of_isClosed ℚ M
      (fun U : I ↦ (U.val : Subgroup (M ≃ₐ[ℚ] M))) (fun U ↦ U.val.isClosed)
  have hLift : IntermediateField.lift (IntermediateField.fixedField
      (ClassFieldTower.ProP.profiniteFrattini (M ≃ₐ[ℚ] M))) =
        ⨆ U : I, IntermediateField.lift
          (IntermediateField.fixedField (U.val : Subgroup (M ≃ₐ[ℚ] M))) := by
    exact (congrArg (fun L : IntermediateField ℚ M ↦ IntermediateField.lift L) hFixed).trans
      (IntermediateField.map_iSup M.val
        (fun U : I ↦ IntermediateField.fixedField (U.val : Subgroup (M ≃ₐ[ℚ] M))))
  have hIndexSup :
      (⨆ U : I, IntermediateField.lift
        (IntermediateField.fixedField (U.val : Subgroup (M ≃ₐ[ℚ] M)))) =
      ⨆ (U : OpenNormalSubgroup (M ≃ₐ[ℚ] M))
        (_ : (U : Subgroup (M ≃ₐ[ℚ] M)).index = 2),
        IntermediateField.lift (IntermediateField.fixedField (U : Subgroup (M ≃ₐ[ℚ] M))) :=
    by
      apply le_antisymm
      · exact iSup_le fun U ↦
          le_iSup_of_le U.val (le_iSup_of_le U.property le_rfl)
      · exact iSup_le fun U ↦ iSup_le fun hU ↦
          le_iSup_of_le (⟨U, hU⟩ : I) le_rfl
  have hResult :
      (⨆ (U : OpenNormalSubgroup (M ≃ₐ[ℚ] M))
        (_ : (U : Subgroup (M ≃ₐ[ℚ] M)).index = 2),
        IntermediateField.lift (IntermediateField.fixedField (U : Subgroup (M ≃ₐ[ℚ] M)))) =
      sawinQuadraticCompositum.toIntermediateField :=
    sawinQuadraticCompositum_eq_iSup_indexTwo_fixedFields.symm
  exact hLift.trans (hIndexSup.trans hResult)

end ClassFieldTower.Sawin
