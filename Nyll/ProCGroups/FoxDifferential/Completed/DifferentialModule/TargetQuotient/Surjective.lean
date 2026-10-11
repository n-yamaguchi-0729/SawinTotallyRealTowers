/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.TargetQuotient.StageMap

/-!
# Fox differential: completed — differential module — target quotient — surjective

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraMap_targetQuotient_lift`
  A noncomputable lift of a completed target group-algebra coefficient to the source completed group
  algebra. The defining equation is
  \(\mathrm{primePowerCompletedGroupAlgebraMap\_targetQuotient\_lift\_spec}\).
- `foxAlgebraicStageTargetQuotientContinuousMonoidHom_surjective`
  The quotient homomorphism \(\mathrm{FreeGroup}(X) \to \mathrm{FreeGroup}(X)/N\) is surjective.
  This specialized form is used to lift coefficients from \(\mathbb{Z}_{\ell}\llbracket
  F/N\rrbracket\) to \(\mathbb{Z}_{\ell}\llbracket F\rrbracket\) in the completed Fox derivative.
- `primePowerCompletedGroupAlgebraMap_targetQuotient_surjective`
  The completed group-algebra map attached to \(\mathrm{FreeGroup}(X) \to \mathrm{FreeGroup}(X)/N\)
  is surjective. This is the coefficient-lifting input for the surjectivity half of \(K/KI \to L\).
- `primePowerCompletedGroupAlgebraMap_targetQuotient_lift_spec`
  The chosen coefficient lift maps back to the prescribed completed target coefficient.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]

omit [DecidableEq X] in
/--
The quotient homomorphism \(\mathrm{FreeGroup}(X) \to \mathrm{FreeGroup}(X)/N\) is surjective.
This specialized form is used to lift coefficients from \(\mathbb{Z}_{\ell}\llbracket
F/N\rrbracket\) to \(\mathbb{Z}_{\ell}\llbracket F\rrbracket\) in the completed Fox derivative.
-/
theorem foxAlgebraicStageTargetQuotientContinuousMonoidHom_surjective
    [TopologicalSpace (FreeGroup X)] [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)] :
    Function.Surjective
      (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) := by
  intro q
  rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
  exact ⟨w, rfl⟩

omit [DecidableEq X] in
/--
The completed group-algebra map attached to \(\mathrm{FreeGroup}(X) \to
\mathrm{FreeGroup}(X)/N\) is surjective. This is the coefficient-lifting input for the
surjectivity half of \(K/KI \to L\).
-/
theorem primePowerCompletedGroupAlgebraMap_targetQuotient_surjective
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)] :
    Function.Surjective
      (primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)) := by
  exact
    primePowerCompletedGroupAlgebraMap_surjective
      (ℓ := ℓ) (G := FreeGroup X)
      (H := foxAlgebraicStageTargetQuotient (X := X) N)
      (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
      (foxAlgebraicStageTargetQuotientContinuousMonoidHom_surjective (X := X) N)

/--
A noncomputable lift of a completed target group-algebra coefficient to the source completed
group algebra. The defining equation is
\(\mathrm{primePowerCompletedGroupAlgebraMap\_targetQuotient\_lift\_spec}\).
-/
def primePowerCompletedGroupAlgebraMap_targetQuotient_lift
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (a : PrimePowerCompletedGroupAlgebra ℓ (foxAlgebraicStageTargetQuotient (X := X) N)) :
    PrimePowerCompletedGroupAlgebra ℓ (FreeGroup X) :=
  Classical.choose
    (primePowerCompletedGroupAlgebraMap_targetQuotient_surjective
      (ℓ := ℓ) (X := X) N a)

omit [DecidableEq X] in
/-- The chosen coefficient lift maps back to the prescribed completed target coefficient. -/
@[simp]
theorem primePowerCompletedGroupAlgebraMap_targetQuotient_lift_spec
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (a : PrimePowerCompletedGroupAlgebra ℓ (foxAlgebraicStageTargetQuotient (X := X) N)) :
    primePowerCompletedGroupAlgebraMap
        (ℓ := ℓ) (G := FreeGroup X)
        (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N)
        (primePowerCompletedGroupAlgebraMap_targetQuotient_lift
          (ℓ := ℓ) (X := X) N a) = a :=
  Classical.choose_spec
    (primePowerCompletedGroupAlgebraMap_targetQuotient_surjective
      (ℓ := ℓ) (X := X) N a)


end

end FoxDifferential
