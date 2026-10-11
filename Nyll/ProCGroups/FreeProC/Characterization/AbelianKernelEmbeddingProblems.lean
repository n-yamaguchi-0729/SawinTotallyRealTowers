/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.Characterization.EmbeddingProblems
import Nyll.ProCGroups.FiniteGroups.Classes

/-!
# Split embedding problems with a condition on the abelian kernel

The finite quotient and covering group are arbitrary finite discrete groups.
Only the kernel of the covering epimorphism belongs to the specified class.
For the Sigma group class this is exactly the split abelian Sigma-kernel
solvability condition; the elementary class gives its elementary variant.
-/

namespace ProCGroups.FreeProC.Characterization

universe u

/-- Every finite split problem with abelian kernel in `C` has a proper
solution. There is no class-membership condition on either whole endpoint. -/
def HasFiniteSplitAbelianKernelEmbeddingSolutions
    (C : ProCGroups.FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  ∀ P : TopologicalEmbeddingProblem G,
    Finite P.A → DiscreteTopology P.A →
      Finite P.B → DiscreteTopology P.B → P.IsSplit →
        C P.α.toMonoidHom.ker →
          (∀ a b : P.α.toMonoidHom.ker, Commute (a : P.A) (b : P.A)) →
            Nonempty P.ProperSolution

end ProCGroups.FreeProC.Characterization
