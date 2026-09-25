/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ProCGroups.ProP.GeneratorRank

set_option autoImplicit false
/-!
# Finite-set presentation of topological generator rank

The LeanEval benchmark presents generator rank as the least cardinality of a
finite topological generating set.  For a topologically finitely generated
profinite group, this agrees with the library's cardinal-valued topological
rank followed by `Cardinal.toNat`.
-/

namespace ClassFieldTower.ProP

open ProCGroups.Generation
open ProCGroups.FiniteGeneration

noncomputable section

universe u

/-- The least cardinality of a finite topological generating set.  This is
the exact presentation used by the LeanEval trusted `generatorRank` helper. -/
noncomputable def finiteTopologicalGeneratorRank
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : ℕ :=
  sInf {k : ℕ | ∃ S : Finset G, S.card = k ∧
    (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}

/-- On a topologically finitely generated profinite group, the finite-set
presentation and the library topological generator rank coincide. -/
theorem finiteTopologicalGeneratorRank_eq_topologicalGeneratorRank
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : TopologicallyFinitelyGenerated G) :
    finiteTopologicalGeneratorRank G = topologicalGeneratorRank G := by
  classical
  let d := topologicalGeneratorRank G
  let C : Set ℕ := {k : ℕ | ∃ S : Finset G, S.card = k ∧
    (Subgroup.closure (S : Set G)).topologicalClosure = ⊤}
  have hrank_lt : topologicalRank G < Cardinal.aleph0 := by
    obtain ⟨S, hS⟩ := hG
    exact (topologicalRank_le_mk_of_topologicallyGenerates hS).trans_lt (by
      have hSmk : Cardinal.mk (S : Set G) = (S.card : Cardinal) :=
        Cardinal.mk_coe_finset
      rw [hSmk]
      exact Cardinal.natCast_lt_aleph0)
  have hcast : (d : Cardinal) = topologicalRank G := by
    exact Cardinal.cast_toNat_of_lt_aleph0 hrank_lt
  have hAtD : TopologicallyGeneratedByAtMost d G :=
    topologicallyGeneratedByAtMost_of_topologicalRank_eq_nat hcast.symm
  obtain ⟨S, hScard, hSgen⟩ := hAtD
  have hdleCard : (d : Cardinal) ≤ (S.card : Cardinal) := by
    rw [hcast]
    calc
      topologicalRank G ≤ Cardinal.mk (S : Set G) :=
        topologicalRank_le_mk_of_topologicallyGenerates hSgen
      _ = (S.card : Cardinal) := Cardinal.mk_coe_finset
  have hdle : d ≤ S.card := by
    exact_mod_cast hdleCard
  have hScardEq : S.card = d := Nat.le_antisymm hScard hdle
  have hdmem : d ∈ C := ⟨S, hScardEq, hSgen⟩
  change sInf C = d
  apply Nat.le_antisymm (Nat.sInf_le hdmem)
  obtain ⟨T, hTcard, hTgen⟩ := Nat.sInf_mem ⟨d, hdmem⟩
  have hdleInfCard : (d : Cardinal) ≤ (sInf C : ℕ) := by
    rw [hcast]
    calc
      topologicalRank G ≤ Cardinal.mk (T : Set G) :=
        topologicalRank_le_mk_of_topologicallyGenerates hTgen
      _ = (T.card : Cardinal) := Cardinal.mk_coe_finset
      _ = (sInf C : ℕ) := by rw [hTcard]
  exact_mod_cast hdleInfCard

end

end ClassFieldTower.ProP
