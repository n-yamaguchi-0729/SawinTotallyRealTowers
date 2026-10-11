/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Completion.ProCIntegerPrimePower
import Nyll.ProCGroups.FreeProC.Basic
import Nyll.ProCGroups.ProC.InverseLimits.Predicates

/-!
# Pro C Groups / Free pro-C / Canonical Data

This module supplies canonical basis maps and proves the rank-one free
pro-\(p\) description of the pro-\(p\) integers.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u

/--
The rank-one basis map converges to the identity in the one-point compactification basis space.
-/
theorem familyConvergesToOneAlongOpenSubgroups_rankOneBasisMap
    {G : Type u} [Group G] [TopologicalSpace G] (g : G) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) (Function.const PUnit g) := by
  exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := G) (Function.const PUnit g)

/-- The rank-one basis map topologically generates the target cyclic pro-\(C\) group. -/
theorem topologicallyGenerates_rankOneBasisMap
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {g : G}
    (hg : Generation.TopologicallyGenerates (G := G) ({g} : Set G)) :
    Generation.TopologicallyGenerates (G := G) (Set.range (Function.const PUnit g)) := by
  have hrange : Set.range (Function.const PUnit g) = ({g} : Set G) := by
    ext y
    simp only [mem_range, Function.const, exists_const, mem_singleton_iff, eq_comm]
  rw [hrange]
  exact hg

/--
The ordinary profinite integers, with their canonical generator, give the expected rank-one
profinite generating datum.
-/
theorem profiniteInteger_rankOneGeneratingData :
    ∃ ι : PUnit →
        Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0})),
      ProCGroups.ProC.HasOpenNormalBasisInClass
        (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0})
        (Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))) ∧
        FamilyConvergesToOneAlongOpenSubgroups (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))) ι ∧
        Generation.TopologicallyGenerates (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0})))
          (Set.range ι) := by
  let G : Type := Multiplicative
    (Completion.ProCIntegerLimitCarrier
      (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))
  let g : G := Completion.proCIntegerOne
    (C := (ProCGroups.FiniteGroupClass.allFinite : ProCGroups.FiniteGroupClass.{0}))
  refine ⟨Function.const PUnit g, ?_, ?_, ?_⟩
  · exact Completion.hasOpenNormalBasisInClass_multiplicative_proCInteger_allFinite
  · exact familyConvergesToOneAlongOpenSubgroups_rankOneBasisMap (G := G) g
  · exact topologicallyGenerates_rankOneBasisMap
      (G := G) (g := g)
      Completion.topologicallyGenerates_singleton_proCIntegerOne_allFinite

/--
The pro-\(p\) integers, with their canonical generator, give the expected rank-one pro-\(p\)
generating datum.
-/
theorem proPInteger_rankOneGeneratingData (p : ℕ) [Fact (Nat.Prime p)] :
    ∃ ι : PUnit →
        Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0})),
      ProCGroups.ProC.HasPGroupOpenNormalBasis p
        (Multiplicative
          (Completion.ProCIntegerLimitCarrier
            (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))) ∧
        FamilyConvergesToOneAlongOpenSubgroups (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))) ι ∧
        Generation.TopologicallyGenerates (G :=
          Multiplicative
            (Completion.ProCIntegerLimitCarrier
              (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0})))
          (Set.range ι) := by
  let G : Type := Multiplicative
    (Completion.ProCIntegerLimitCarrier
      (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))
  let g : G := Completion.proCIntegerOne
    (C := (ProCGroups.FiniteGroupClass.pGroup p : ProCGroups.FiniteGroupClass.{0}))
  refine ⟨Function.const PUnit g, ?_, ?_, ?_⟩
  · exact Completion.hasPGroupOpenNormalBasis_multiplicative_proCInteger_pGroup (p := p)
  · exact familyConvergesToOneAlongOpenSubgroups_rankOneBasisMap (G := G) g
  · exact topologicallyGenerates_rankOneBasisMap
      (G := G) (g := g)
      (Completion.topologicallyGenerates_singleton_proCIntegerOne_pGroup (p := p))

end ProCGroups.FreeProC
