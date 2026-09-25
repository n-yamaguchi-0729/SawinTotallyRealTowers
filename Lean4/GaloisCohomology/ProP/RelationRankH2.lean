/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.PresentationH2LowerBound
import GaloisCohomology.ProP.PresentationH2UpperBound

set_option autoImplicit false
/-!
# Minimal relation rank and degree-two continuous cohomology

The upper and lower presentation bounds identify the least relation count of a
finitely minimally presented pro-`p` group with the dimension of its continuous
degree-two cohomology with trivial `ZMod p` coefficients.
-/

open scoped Topology

namespace ClassFieldTower.ProP

noncomputable section

universe u

/-- The dimension of continuous degree-two cohomology with trivial `ZMod p` coefficients. -/
noncomputable def h2Rank (p : ℕ)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  Module.finrank (ZMod p)
    (Cohomology.continuousCohomologyZModPLifted p G 2)

@[simp] theorem h2Rank_eq_finrank
    {p : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    h2Rank p G = Module.finrank (ZMod p)
      (Cohomology.continuousCohomologyZModPLifted p G 2) :=
  rfl

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- For a finitely minimally presented pro-`p` group, relation rank equals H² rank. -/
theorem minimalRelationRank_eq_h2Rank
    (hG : HasFiniteMinimalPresentation p G) :
    minimalRelationRank p G hG = h2Rank p G := by
  obtain ⟨sourceData, d, P, hP⟩ :=
    exists_presentation_relationCard_eq_minimal hG
  let _ := presentationH2_finiteDimensional P
  apply Nat.le_antisymm
  · simpa [h2Rank] using
      presentation_relationCard_le_finrank_h2 hG P hP rfl
  · simpa [h2Rank] using
      finrank_continuousCohomologyZModPLifted_degree_two_le_relationCard P

end

end ClassFieldTower.ProP
