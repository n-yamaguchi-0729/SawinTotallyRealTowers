/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InducedFunctions
import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.SemidirectProduct

/-!
# Evaluation on induced semidirect products

The subgroup action on the induced group is the restriction of its ambient
translation action. Evaluation at the identity therefore induces an actual
surjective homomorphism of semidirect products.
-/

namespace ProCGroups.InducedFunctions

universe uQ uA

variable {Q : Type uQ} [Group Q] {A : Type uA} [CommGroup A]
variable (J : Subgroup Q) [MulDistribMulAction J A]

/-- Evaluation on the function coordinate, with the subgroup coordinate
unchanged, defines a homomorphism of the actual semidirect products. -/
def inducedEvaluationSemidirectHom :
    (InducedModule (B := A) J) ⋊[
        (MulDistribMulAction.toMulAut Q (InducedModule (B := A) J)).comp J.subtype] J →*
      A ⋊[MulDistribMulAction.toMulAut J A] J :=
  SemidirectProduct.map (inducedEvaluation J) (MonoidHom.id J) (by
    intro j
    apply MonoidHom.ext
    intro f
    change inducedEvaluation J ((j : Q) • f) = j • inducedEvaluation J f
    exact inducedEvaluation_smul J j f)

/-- The semidirect-product map evaluates exactly the induced-function
coordinate and preserves the second coordinate. -/
theorem inducedEvaluationSemidirectHom_apply
    (f : InducedModule (B := A) J) (j : J) :
    inducedEvaluationSemidirectHom J ⟨f, j⟩ = ⟨inducedEvaluation J f, j⟩ := by
  rfl

/-- Every pair has a preimage, supplied by the actual evaluation epimorphism. -/
theorem inducedEvaluationSemidirectHom_surjective :
    Function.Surjective (inducedEvaluationSemidirectHom (A := A) J) := by
  intro x
  obtain ⟨f, hf⟩ := inducedEvaluation_surjective (B := A) J x.left
  refine ⟨⟨f, x.right⟩, ?_⟩
  apply SemidirectProduct.ext
  · change inducedEvaluation J f = x.left
    exact hf
  · rfl

end ProCGroups.InducedFunctions
