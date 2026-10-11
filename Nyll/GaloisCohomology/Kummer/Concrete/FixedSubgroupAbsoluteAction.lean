/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-!
# The fixed-subgroup action and the absolute Galois action

For a finite normal intermediate field, the actual quotient conjugation action
on its fixing subgroup agrees with the canonical absolute Galois action after
a constructed continuous comparison of the abelianizations.
-/

namespace KummerTheory

open ProCGroups.Abelian

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  (L : IntermediateField K Ω) [FiniteDimensional K L]

local instance closureOverIntermediate : IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed K, Algebra.IsAlgebraic.tower_top (K := K) L⟩

/-- Compare the actual fixing subgroup's abelianization with the absolute
Galois abelianization of the intermediate field. -/
noncomputable def fixingSubgroupAbsoluteAbelianizationEquiv :
    _root_.TopologicalAbelianization L.fixingSubgroup ≃ₜ*
      _root_.TopologicalAbelianization Gal(AlgebraicClosure L/L) :=
  (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L)).trans
    (absoluteGaloisClosureAbelianizationEquiv L Ω)

/-- Evaluation of the comparison on a fixing-subgroup representative. -/
theorem fixingSubgroupAbsoluteAbelianizationEquiv_apply_mk (σ : L.fixingSubgroup) :
    fixingSubgroupAbsoluteAbelianizationEquiv L
        (TopologicalAbelianization.mk L.fixingSubgroup σ) =
      TopologicalAbelianization.mk Gal(AlgebraicClosure L/L)
        (absoluteGaloisClosureEquiv L Ω (fixingSubgroupContinuousEquiv L σ)) := by
  rw [fixingSubgroupAbsoluteAbelianizationEquiv, ContinuousMulEquiv.trans_apply,
    TopologicalAbelianization.congr_apply_mk]
  exact TopologicalAbelianization.congr_apply_mk
    (absoluteGaloisClosureEquiv L Ω) (fixingSubgroupContinuousEquiv L σ)

variable [Normal K L]

attribute [local instance] fixingSubgroup_normal

/-- Under the constructed comparison, the quotient action on the actual
normal fixing subgroup is the action of the restricted field automorphism. -/
theorem fixingSubgroupAbsoluteAbelianizationEquiv_quotient_conjugation
    (σ : Gal(Ω/K)) (x : _root_.TopologicalAbelianization L.fixingSubgroup) :
    fixingSubgroupAbsoluteAbelianizationEquiv L
        (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup
          (QuotientGroup.mk' L.fixingSubgroup σ) x) =
      absoluteGaloisAbelianizationAction (σ.restrictNormal L).toRingEquiv
        (fixingSubgroupAbsoluteAbelianizationEquiv L x) := by
  change absoluteGaloisClosureAbelianizationEquiv L Ω
      (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L)
        (quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup
          (QuotientGroup.mk' L.fixingSubgroup σ) x)) = _
  rw [fixingSubgroupAbelianization_conjugation]
  exact absoluteGaloisClosureAbelianizationEquiv_conjugation L Ω
    (σ.restrictNormal L).toRingEquiv σ.toRingEquiv
    (galois_restrictNormal_algebraMap L σ)
    (TopologicalAbelianization.congr (fixingSubgroupContinuousEquiv L) x)

/-- Nontriviality of the canonical absolute action detects the corresponding
element of the quotient conjugation action on the fixing subgroup. -/
theorem fixingSubgroup_quotient_action_ne_one_of_absolute_action_ne_one
    (σ : Gal(Ω/K))
    (hσ : absoluteGaloisAbelianizationAction (σ.restrictNormal L).toRingEquiv ≠ 1) :
    quotientConjugationTopologicalAbelianizationMap L.fixingSubgroup
      (QuotientGroup.mk' L.fixingSubgroup σ) ≠ 1 := by
  intro h
  apply hσ
  apply MulEquiv.ext
  intro a
  obtain ⟨x, rfl⟩ := (fixingSubgroupAbsoluteAbelianizationEquiv L).surjective a
  have heq := fixingSubgroupAbsoluteAbelianizationEquiv_quotient_conjugation L σ x
  rw [h, MulAut.one_apply] at heq
  exact heq.symm

end KummerTheory
