/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Basic
import Nyll.ProCGroups.TopologicalGroups

/-!
# Pro C Groups / Free pro-C / Characterization / Embedding Problems

This module defines topological embedding problems, their weak and proper
solutions, and the finite split lifting properties used in freeness criteria.
-/

namespace ProCGroups.FreeProC.Characterization

open ProCGroups.FreeProC

universe u

section EmbeddingProblems

/-- A topological embedding problem for a topological group. Finiteness and finite-class
conditions are expressed by the predicates below instead of parallel wrapper structures. -/
structure TopologicalEmbeddingProblem
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  /-- The covering topological group through which a solution must lift. -/
  A : TopGrp.{u}
  /-- The common target of the embedding-problem epimorphism and the prescribed map from `G`. -/
  B : TopGrp.{u}
  /-- The continuous homomorphism from the covering group `A` onto `B`. -/
  α : A →ₜ* B
  /-- The covering homomorphism `α` is surjective. -/
  surjective_α : Function.Surjective α
  /-- The prescribed continuous homomorphism from `G` to the target group `B`. -/
  φ : G →ₜ* B
  /-- The prescribed map `φ` is surjective, so the embedding problem is epimorphic on both legs. -/
  surjective_φ : Function.Surjective φ

namespace TopologicalEmbeddingProblem

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A proper solution is a surjective weak solution. -/
def ProperSolution (P : TopologicalEmbeddingProblem G) : Type u :=
  { φbar : G →ₜ* P.A //
    Function.Surjective φbar ∧ P.α.comp φbar = P.φ }

/-- The embedding problem is split: its epimorphism has a continuous section. -/
def IsSplit (P : TopologicalEmbeddingProblem G) : Prop :=
  ∃ σ : P.B →ₜ* P.A, P.α.comp σ = ContinuousMonoidHom.id P.B

/--
An embedding problem has at least \(\kappa\) different solutions if there is a family of
pairwise distinct continuous surjective lifts indexed by a set of cardinality \(\kappa\).
-/
def HasAtLeastProperSolutions
    (P : TopologicalEmbeddingProblem G) (κ : Cardinal) : Prop :=
  ∃ I : Type u, Cardinal.mk I = κ ∧
    ∃ ψ : I → P.ProperSolution, Function.Injective ψ

end TopologicalEmbeddingProblem

/-- A finite embedding problem whose two finite target groups lie in the chosen finite class. -/
def IsFiniteCEmbeddingProblem
    (C : ProCGroups.FiniteGroupClass.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : TopologicalEmbeddingProblem G) : Prop :=
  Finite P.A ∧ DiscreteTopology P.A ∧ C P.A ∧
    Finite P.B ∧ DiscreteTopology P.B ∧ C P.B

/-- A finite \(C\)-embedding problem with a continuous section. -/
def IsFiniteSplitCEmbeddingProblem
    (C : ProCGroups.FiniteGroupClass.{u})
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (P : TopologicalEmbeddingProblem G) : Prop :=
  IsFiniteCEmbeddingProblem C P ∧ P.IsSplit

end EmbeddingProblems

end ProCGroups.FreeProC.Characterization
