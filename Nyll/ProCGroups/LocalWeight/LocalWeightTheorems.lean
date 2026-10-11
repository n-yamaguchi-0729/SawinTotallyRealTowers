/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.LocalWeight.ClosedNormalDataAndTransfiniteSeries

/-!
# Local weight from convergent generating sets

This file identifies local weight with the clopen invariant `rho` in the presence of a closed
generating set, and computes the cardinality of an infinite generating set that converges to the
identity along open subgroups.
-/

open Set
open TopologicalSpace
open Order
open scoped Cardinal
open scoped Topology Pointwise

namespace ProCGroups.LocalWeight

universe u

open ProCGroups.ProC ProCGroups.Generation
open ProCGroups.FiniteGeneration


/-- 6.2(a). Closed generating subsets compute the local weight. -/
theorem localWeight_eq_rho_of_closedGeneratingSet
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (X : Set G) (hXclosed : IsClosed X)
    (hXgen : TopologicallyGenerates (G := G) X) (hXinfinite : Set.Infinite X) :
    localWeight G = rho ↥X := by
  have hGinf : Infinite G := by
    classical
    by_contra hfin
    let : Finite G := not_infinite_iff_finite.mp hfin
    exact hXinfinite (Set.toFinite X)
  have hle : localWeight G ≤ rho ↥X :=
    localWeight_le_rho_of_closedGeneratingSet
      (G := G) X hXclosed hXgen hXinfinite
  have hrho_le : rho ↥X ≤ localWeight G := by
    have hBasis : TopologicalSpace.IsTopologicalBasis { U : Set G | IsClopen U } :=
      ProCGroups.InverseSystems.isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected
    calc
      rho ↥X ≤ rho G :=
        rho_subtype_le_rho_of_closed (X := G) (A := X) hXclosed
      _ = weight G := (weight_eq_rho_of_clopenBasis (X := G) hBasis).symm
      _ = localWeight G :=
        (localWeight_eq_weight_of_infinite_profiniteGroup (G := G)).symm
  exact le_antisymm hle hrho_le

/-- 6.2(b). Infinite generating sets converging to \(1\) have cardinality \(w_0(G)\). -/
theorem cardinalEqLocalWeight_of_generatesAndConvergesToOneAlongOpenSubgroups_infinite
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (X : Set G)
    (hX : GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X) (hXinfinite : Set.Infinite X) :
    Cardinal.mk X = localWeight G := by
  have hclosure : closure X = X ∪ ({1} : Set G) := by
    exact (closure_generatorsConvergingToOne (G := G) hX.2).2 hXinfinite
  have hClosureInf : Set.Infinite (closure X) := by
    by_contra hfin
    exact hXinfinite ((Set.not_infinite.mp hfin).subset subset_closure)
  have hClosureGen : TopologicallyGenerates (G := G) (closure X) := by
    exact (topologicallyGenerates_closure_iff (G := G) (X := X)).1 hX.1
  have hClosureClosed : IsClosed (closure X) := isClosed_closure
  calc
    Cardinal.mk X = rho ↥(closure X) := by
      symm
      exact rho_closure_eq_cardinal_of_generatesAndConvergesToOneAlongOpenSubgroups_infinite
        (G := G) X hX hXinfinite hclosure
    _ = localWeight G := by
      simpa using
        (localWeight_eq_rho_of_closedGeneratingSet
          (G := G) (closure X) hClosureClosed hClosureGen hClosureInf).symm




end ProCGroups.LocalWeight
