/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.SeparableGaloisClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# The fixing-subgroup action through a separable closure

For a finite normal intermediate field in a separable closure, the actual
quotient conjugation action
on its fixing subgroup agrees with the canonical absolute Galois action after
a constructed continuous comparison of the abelianizations.
-/

namespace KummerTheory

open ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]

local instance separableClosureOverIntermediate : IsSepClosure L Ω :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ω⟩

/-- Compare the actual fixing subgroup's abelianization with the absolute
Galois abelianization of the intermediate field. -/
noncomputable def fixingSubgroupSeparableAbsoluteAbelianizationEquiv :
    _root_.TopologicalAbelianization L.fixingSubgroup ≃ₜ*
      _root_.TopologicalAbelianization Gal(AlgebraicClosure L/L) :=
  (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L)).trans
    (separableAbsoluteGaloisClosureAbelianizationEquiv L Ω)

/-- Evaluation of the comparison on a fixing-subgroup representative. -/
theorem fixingSubgroupSeparableAbsoluteAbelianizationEquiv_apply_mk (σ : L.fixingSubgroup) :
    fixingSubgroupSeparableAbsoluteAbelianizationEquiv L
        (TopologicalAbelianization.mk L.fixingSubgroup σ) =
      TopologicalAbelianization.mk Gal(AlgebraicClosure L/L)
        (separableAbsoluteGaloisClosureEquiv L Ω (fixingSubgroupContinuousEquiv L σ)) := by
  rw [fixingSubgroupSeparableAbsoluteAbelianizationEquiv, ContinuousMulEquiv.trans_apply,
    TopologicalAbelianization.congr_apply_mk]
  exact TopologicalAbelianization.congr_apply_mk
    (separableAbsoluteGaloisClosureEquiv L Ω) (fixingSubgroupContinuousEquiv L σ)

variable [Normal K L]

attribute [local instance] fixingSubgroup_normal

/-- Under the constructed comparison, the quotient action on the actual
normal fixing subgroup is the action of the restricted field automorphism. -/
theorem fixingSubgroupSeparableAbsoluteAbelianizationEquiv_quotient_conjugation
    (σ : Gal(Ω/K)) (x : _root_.TopologicalAbelianization L.fixingSubgroup) :
    fixingSubgroupSeparableAbsoluteAbelianizationEquiv L
        (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup
          (QuotientGroup.mk' L.fixingSubgroup σ) x) =
      absoluteGaloisAbelianizationAction (σ.restrictNormal L).toRingEquiv
        (fixingSubgroupSeparableAbsoluteAbelianizationEquiv L x) := by
  change separableAbsoluteGaloisClosureAbelianizationEquiv L Ω
      (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L)
        (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup
          (QuotientGroup.mk' L.fixingSubgroup σ) x)) = _
  rw [fixingSubgroupAbelianization_conjugation]
  exact separableAbsoluteGaloisClosureAbelianizationEquiv_conjugation L Ω
    (σ.restrictNormal L).toRingEquiv σ.toRingEquiv
    (galois_restrictNormal_algebraMap L σ)
    (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L) x)

end KummerTheory
