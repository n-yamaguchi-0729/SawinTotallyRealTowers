import SawinTotallyRealTowers.RealProPOpenNormalStage
import SawinTotallyRealTowers.SixPrimeQuadraticClassification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.Topology.Algebra.OpenSubgroup

set_option autoImplicit false

/-!
# Index-two fixed fields of the real pro-two extension

Finite Galois layers inside the maximal real extension correspond to open
normal subgroups. Restricting and then lifting recovers the original
ambient field. The index-degree equality identifies its quadratic layers,
whose compositum has already been determined arithmetically.
-/

namespace ClassFieldTower.Sawin

private theorem exists_indexTwo_fixedField_of_quadratic_le
    (M : IntermediateField ℚ (AlgebraicClosure ℚ)) [IsGalois ℚ M]
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hDegree : Module.finrank ℚ E = 2) (hEM : E.toIntermediateField ≤ M) :
    ∃ U : OpenNormalSubgroup (M ≃ₐ[ℚ] M),
      (U : Subgroup (M ≃ₐ[ℚ] M)).index = 2 ∧
        IntermediateField.lift (IntermediateField.fixedField (U : Subgroup (M ≃ₐ[ℚ] M))) =
          E.toIntermediateField := by
  let R : IntermediateField ℚ M := IntermediateField.restrict hEM
  let e : E.toIntermediateField ≃ₐ[ℚ] R := IntermediateField.restrictAlgEquiv hEM
  let : FiniteDimensional ℚ R := e.toLinearEquiv.finiteDimensional
  have hIndex : R.fixingSubgroup.index = 2 :=
    (IntermediateField.finrank_eq_fixingSubgroup_index M R).symm.trans
      (e.toLinearEquiv.finrank_eq.symm.trans hDegree)
  let U : OpenNormalSubgroup (M ≃ₐ[ℚ] M) :=
    { toSubgroup := R.fixingSubgroup
      isOpen' := (InfiniteGalois.isOpen_iff_finite R).mpr inferInstance
      isNormal' := R.fixingSubgroup.normal_of_index_eq_two hIndex }
  refine ⟨U, hIndex, ?_⟩
  have hFixed : IntermediateField.fixedField R.fixingSubgroup = R :=
    InfiniteGalois.fixedField_fixingSubgroup R
  exact (congrArg (fun L : IntermediateField ℚ M ↦ IntermediateField.lift L) hFixed).trans
    (IntermediateField.lift_restrict hEM)

/-- The ambient compositum of index-two open-normal fixed fields is exactly
the concrete compositum of the five admissible quadratic extensions. -/
theorem sawinQuadraticCompositum_eq_iSup_indexTwo_fixedFields :
    sawinQuadraticCompositum.toIntermediateField =
      ⨆ (U : OpenNormalSubgroup
          (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
            maximalRealProPOutside 2 sawinRationalPrimeSupport))
        (_ : (U : Subgroup
          (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
            maximalRealProPOutside 2 sawinRationalPrimeSupport)).index = 2),
        IntermediateField.lift (IntermediateField.fixedField
          (U : Subgroup
            (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
              maximalRealProPOutside 2 sawinRationalPrimeSupport))) := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    maximalRealProPOutside 2 sawinRationalPrimeSupport
  let : IsGalois ℚ M := maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport
  change sawinQuadraticCompositum.toIntermediateField =
    ⨆ (U : OpenNormalSubgroup (M ≃ₐ[ℚ] M))
      (_ : (U : Subgroup (M ≃ₐ[ℚ] M)).index = 2),
      IntermediateField.lift (IntermediateField.fixedField (U : Subgroup (M ≃ₐ[ℚ] M)))
  apply le_antisymm
  · rw [sawinQuadraticCompositum_eq_iSup_quadratic_layers]
    refine iSup_le fun E ↦ iSup_le fun hE ↦ iSup_le fun hDegree ↦ ?_
    have hEM : E.toIntermediateField ≤ M := le_maximalRealProPOutside ⟨E, hE⟩
    have hExists : ∃ U : OpenNormalSubgroup (M ≃ₐ[ℚ] M),
        (U : Subgroup (M ≃ₐ[ℚ] M)).index = 2 ∧
          IntermediateField.lift (IntermediateField.fixedField
            (U : Subgroup (M ≃ₐ[ℚ] M))) = E.toIntermediateField :=
      exists_indexTwo_fixedField_of_quadratic_le M E hDegree hEM
    obtain ⟨U, hIndex, hField⟩ := hExists
    apply le_iSup_of_le U
    apply le_iSup_of_le hIndex
    rw [hField]
  · refine iSup_le fun U ↦ iSup_le fun hIndex ↦ ?_
    let S : FiniteRealPExtension 2 sawinRationalPrimeSupport :=
      realProPOpenNormalStage 2 sawinRationalPrimeSupport U
    have hDegree : Module.finrank ℚ S.val = 2 := by
      let : IsGalois ℚ S.val.toIntermediateField := S.val.isGalois
      calc
        Module.finrank ℚ S.val = Nat.card (S.val ≃ₐ[ℚ] S.val) :=
          (IsGalois.card_aut_eq_finrank ℚ S.val).symm
        _ = Nat.card ((M ≃ₐ[ℚ] M) ⧸ (U : Subgroup (M ≃ₐ[ℚ] M))) :=
          (Nat.card_congr (realProPOpenNormalQuotientEquivStage
            2 sawinRationalPrimeSupport U).toEquiv).symm
        _ = (U : Subgroup (M ≃ₐ[ℚ] M)).index := (Subgroup.index_eq_card _).symm
        _ = 2 := hIndex
    have hLayer : S.val ≤ sawinQuadraticCompositum :=
      admissible_quadratic_le_sawinQuadraticCompositum S.val hDegree S.property
    rw [← realProPOpenNormalStage_field 2 sawinRationalPrimeSupport U]
    exact hLayer

end ClassFieldTower.Sawin
