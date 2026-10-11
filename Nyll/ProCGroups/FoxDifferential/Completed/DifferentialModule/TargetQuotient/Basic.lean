/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.DifferentialModule.Map.Surjective
import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Source.Index

/-!
# Fox differential: completed — differential module — target quotient — basic

The principal declarations in this module are:

- `foxAlgebraicStageTargetQuotientContinuousMonoidHom`
  The completed Fox-differential map is continuous with respect to the inverse-limit topology on the
  completed coefficient modules.
- `foxAlgebraicStageTargetQuotientContinuousMonoidHom_apply`
  The finite-stage target quotient homomorphism sends a word to its quotient class modulo \(N\).
- `foxAlgebraicStagePrimePowerSourceCompletedIndex_le_targetQuotientComap`
  The completed free derivative source finite stage \([N,N]N^{ell^a}\) refines every finite stage
  pulled back from the target quotient \(F/N\). This order comparison lets the completed
  group-algebra projection for \(\pi: \mathbb{Z}_{\ell}\llbracket F\rrbracket \to
  \mathbb{Z}_{\ell}\llbracket F/N\rrbracket\) be computed from the completed free derivative source
  projection.
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

/--
The completed Fox-differential map is continuous with respect to the inverse-limit topology on
the completed coefficient modules.
-/
def foxAlgebraicStageTargetQuotientContinuousMonoidHom
    [TopologicalSpace (FreeGroup X)] [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)] :
    ContinuousMonoidHom (FreeGroup X) (foxAlgebraicStageTargetQuotient (X := X) N) where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := continuous_of_discreteTopology

omit [DecidableEq X] in
/--
The finite-stage target quotient homomorphism sends a word to its quotient class modulo \(N\).
-/
@[simp]
theorem foxAlgebraicStageTargetQuotientContinuousMonoidHom_apply
    [TopologicalSpace (FreeGroup X)] [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    (w : FreeGroup X) :
    foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N w =
      QuotientGroup.mk' N w := rfl

omit [DecidableEq X] [Fact (0 < ℓ)] in
/--
The completed free derivative source finite stage \([N,N]N^{ell^a}\) refines every finite stage
pulled back from the target quotient \(F/N\). This order comparison lets the completed
group-algebra projection for \(\pi: \mathbb{Z}_{\ell}\llbracket F\rrbracket \to
\mathbb{Z}_{\ell}\llbracket F/N\rrbracket\) be computed from the completed free derivative
source projection.
-/
theorem foxAlgebraicStagePrimePowerSourceCompletedIndex_le_targetQuotientComap
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) [N.Normal]
    [TopologicalSpace (foxAlgebraicStageTargetQuotient (X := X) N)]
    [IsTopologicalGroup (foxAlgebraicStageTargetQuotient (X := X) N)]
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (j : PrimePowerCompletedGroupAlgebraIndex
      (foxAlgebraicStageTargetQuotient (X := X) N)) :
    completedGroupAlgebraComapIndex
        (G := FreeGroup X) (H := foxAlgebraicStageTargetQuotient (X := X) N)
        (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N) j.2 ≤
      foxAlgebraicStagePrimePowerSourceCompletedIndex
        (ℓ := ℓ) (X := X) N hfinite j.1 := by
  change foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ j.1) ≤
    Subgroup.comap
      (foxAlgebraicStageTargetQuotientContinuousMonoidHom (X := X) N).toMonoidHom
      (((OrderDual.ofDual j.2).1 :
        OpenNormalSubgroup (foxAlgebraicStageTargetQuotient (X := X) N)) :
        Subgroup (foxAlgebraicStageTargetQuotient (X := X) N))
  intro g hg
  change QuotientGroup.mk' N g ∈
    (((OrderDual.ofDual j.2).1 :
      OpenNormalSubgroup (foxAlgebraicStageTargetQuotient (X := X) N)) :
      Subgroup (foxAlgebraicStageTargetQuotient (X := X) N))
  have hgN : g ∈ N :=
    foxCommutatorPowerSubgroup_le_normal (F := FreeGroup X) N (ℓ ^ j.1) hg
  have hgq : QuotientGroup.mk' N g =
      (1 : foxAlgebraicStageTargetQuotient (X := X) N) := by
    simpa using (QuotientGroup.eq_one_iff (N := N) g).2 hgN
  rw [hgq]
  exact Subgroup.one_mem _


end

end FoxDifferential
