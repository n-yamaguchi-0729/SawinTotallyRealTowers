/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.LocalWeight.LocalWeightTheorems

/-!
# Generating sets converging to one

Countable descending open-normal bases are characterized by generating sets that converge to the
identity along open subgroups. For nonempty profinite groups this yields a characterization of
metrizability by a countable convergent generating set.
-/

open Set
open TopologicalSpace
open Order
open scoped Cardinal
open scoped Topology Pointwise

namespace ProCGroups.LocalWeight

universe u

open ProCGroups.Generation ProCGroups.ProC ProCGroups.FiniteGeneration


/--
A generating set converging to \(1\) is countable exactly when the profinite group admits a
countable descending open-normal chain at the identity.
-/
theorem cardinal_le_aleph0_iff_hasCountableDescendingOpenNormalChainAtOne
    {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (X : Set G) (hX : GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X) :
    Cardinal.mk X ≤ ℵ₀ ↔
      ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
  constructor
  · intro hXcount
    by_cases hXinfinite : Set.Infinite X
    · have hlocal : localWeight G ≤ ℵ₀ := by
        simpa [cardinalEqLocalWeight_of_generatesAndConvergesToOneAlongOpenSubgroups_infinite
          (G := G) X hX hXinfinite] using hXcount
      exact hasCountableDescendingOpenNormalChainAtOne_of_localWeight_le_aleph0
        (G := G) hlocal
    · let : Finite X := Set.not_infinite.mp hXinfinite
      have hXfinite : X.Finite := Set.toFinite X
      let s : Finset G := hXfinite.toFinset
      have hsgen : TopologicallyFinitelyGenerated G := by
        refine ⟨s, ?_⟩
        simpa [s] using hX.1
      exact hasCountableDescendingOpenNormalChainAtOne_of_topologicallyFinitelyGenerated
        (G := G) hsgen
  · intro hchain
    rcases hchain with ⟨U, _hUanti, hUbasis⟩
    have hBasis : IsNeighborhoodBasisAt (X := G) (1 : G)
        (Set.range fun n : ℕ => (((U n : Subgroup G) : Set G))) := by
      constructor
      · intro V hV
        rcases hV with ⟨n, rfl⟩
        exact ⟨openNormalSubgroup_isOpen (G := G) (U n), (U n).one_mem'⟩
      · intro V hVopen h1V
        rcases hUbasis V hVopen h1V with ⟨n, hnV⟩
        exact ⟨((U n : Subgroup G) : Set G), ⟨n, rfl⟩, hnV⟩
    have hlocal : localWeight G ≤ ℵ₀ := by
      calc
        localWeight G ≤
            familyCardinal (X := G) (Set.range fun n : ℕ => (((U n : Subgroup G) : Set G))) := by
          simpa [localWeight] using
            localWeightAt_le_familyCardinal_of_basis (X := G) (x := (1 : G)) hBasis
        _ ≤ ℵ₀ := by
          unfold familyCardinal
          exact Cardinal.mk_le_aleph0_iff.mpr
            (Set.countable_range (fun n : ℕ => (((U n : Subgroup G) : Set G))))
    by_cases hXinfinite : Set.Infinite X
    · calc
        Cardinal.mk X = localWeight G :=
          cardinalEqLocalWeight_of_generatesAndConvergesToOneAlongOpenSubgroups_infinite
            (G := G) X hX hXinfinite
        _ ≤ ℵ₀ := hlocal
    · let : Finite X := Set.not_infinite.mp hXinfinite
      exact ((Cardinal.lt_aleph0_iff_finite (α := X)).2 inferInstance).le

/--
A profinite group is metrizable exactly when it admits a countable generating set converging to
\(1\).
-/
theorem nonempty_metrizableSpace_iff_exists_countable_generatingSetConvergingToOne
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Nonempty (MetrizableSpace G) ↔
      ∃ X : Set G, GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) X ∧ Countable X := by
  constructor
  · intro hmetr
    rcases exists_generatorsConvergingToOne (G := G) with ⟨X, hX⟩
    refine ⟨X, hX, ?_⟩
    have hchain : ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
      exact (metrizable_iff_hasCountableDescendingOpenNormalChainAtOne
        (G := G)).1 hmetr
    have hXcount : Cardinal.mk X ≤ ℵ₀ := by
      exact
        ((cardinal_le_aleph0_iff_hasCountableDescendingOpenNormalChainAtOne
            (G := G) X hX)).2 hchain
    exact Cardinal.mk_le_aleph0_iff.mp hXcount
  · rintro ⟨X, hX, hXcount⟩
    have hchain : ProCGroups.ProC.HasCountableOpenNormalBasisAtOne G := by
      exact
        ((cardinal_le_aleph0_iff_hasCountableDescendingOpenNormalChainAtOne
            (G := G) X hX)).1
          (Cardinal.mk_le_aleph0_iff.mpr hXcount)
    exact (metrizable_iff_hasCountableDescendingOpenNormalChainAtOne
      (G := G)).2 hchain

end ProCGroups.LocalWeight
