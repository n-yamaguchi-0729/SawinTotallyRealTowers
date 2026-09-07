import ProCGroups.FoxDifferential.Completed.Continuous.Universal.FiniteStage

set_option autoImplicit false

/-!
# Finite-stage relation reflection for completed Fox differentials

This module records the elementary equivalence between membership in a
finite-stage relation submodule and vanishing in its quotient.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

universe u

/--
A pre-stage reduction is a finite relation exactly when its finite
universal-module class is zero.
-/
theorem zcCompletedDifferentialModulePreStageMap_relation_iff_stage_mkQ_eq_zero
    {C : ProCGroups.FiniteGroupClass.{u}}
    {G H : Type u} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {ψ : G →* H}
    {i : ZCCompletedDifferentialModuleIndex C ψ}
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G} :
    zcCompletedDifferentialModulePreStageMap C ψ i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i) ↔
      ((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
        (zcCompletedDifferentialModulePreStageMap C ψ i x) = 0) := by
  constructor
  · intro hx
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).2 hx
  · intro hx
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).1 hx

end

end CrowellExactSequence
