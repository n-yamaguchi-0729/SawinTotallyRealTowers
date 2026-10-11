/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.Basic
import Nyll.ProCGroups.ProC.Kernels

/-!
# Abelianizations inside finite-step solvable quotients

This module studies the last closed-derived subgroup of a maximal solvable quotient and formulates
torsion-freeness and containment conditions using abelianizations of its open subgroups.
-/

open scoped Topology

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian

universe u

/-- The last nontrivial closed derived term inside the maximal \(m\)-step solvable quotient. -/
def lastDerivedSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) : Subgroup (MaxSolvQuot G m) :=
  topDerivedTop (MaxSolvQuot G m) (m - 1)

/-- An open subgroup of the maximal \(m\)-step solvable quotient contains the last derived term. -/
def aboveLastDerived
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ) (H : OpenSubgroup (MaxSolvQuot G m)) : Prop :=
  lastDerivedSubgroup (G := G) m ≤ (H : Subgroup (MaxSolvQuot G m))

/--
An open normal subgroup inside an open subgroup of the maximal \(m\)-step solvable quotient
contains the last derived term.
-/
def containsLastDerived
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (m : ℕ)
    (H : OpenSubgroup (MaxSolvQuot G m))
    (N : OpenNormalSubgroup ↥(H : Subgroup (MaxSolvQuot G m))) : Prop :=
  ∀ x : MaxSolvQuot G m, x ∈ lastDerivedSubgroup (G := G) m →
    ∃ hxH : x ∈ H, (⟨x, hxH⟩ : H) ∈ N

/--
\(\mathrm{ContainsLastDerived}\) is the intrinsic form of saying that the ambient image of \(N\)
contains the last derived subgroup.
-/
theorem containsLastDerived_iff_lastDerivedSubgroup_le_map_subtype
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ}
    {H : OpenSubgroup (MaxSolvQuot G m)}
    {N : OpenNormalSubgroup ↥(H : Subgroup (MaxSolvQuot G m))} :
    containsLastDerived (G := G) m H N ↔
      lastDerivedSubgroup (G := G) m ≤
        (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m))).map
          ((H : Subgroup (MaxSolvQuot G m)).subtype) := by
  constructor
  · intro h x hx
    rcases h x hx with ⟨hxH, hxN⟩
    exact ⟨⟨x, hxH⟩, hxN, rfl⟩
  · intro h x hx
    rcases h hx with ⟨y, hyN, hyx⟩
    refine ⟨by simp only [← hyx, Subgroup.subtype_apply, SetLike.coe_mem], ?_⟩
    have hy : (⟨x, by simp only [← hyx, Subgroup.subtype_apply, y.2]⟩ :
        ↥(H : Subgroup (MaxSolvQuot G m))) = y := by
      exact Subtype.ext hyx.symm
    change
      (⟨x, by simp only [← hyx, Subgroup.subtype_apply, y.2]⟩ :
          ↥(H : Subgroup (MaxSolvQuot G m))) ∈
        (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m)))
    rw [hy]
    exact hyN

/--
The quotient contains the last derived subgroup under the stated map-subtype containment
hypothesis.
-/
theorem containsLastDerived_of_lastDerivedSubgroup_le_map_subtype
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {m : ℕ}
    {H : OpenSubgroup (MaxSolvQuot G m)}
    {N : OpenNormalSubgroup ↥(H : Subgroup (MaxSolvQuot G m))}
    (hN :
      lastDerivedSubgroup (G := G) m ≤
        (N : Subgroup ↥(H : Subgroup (MaxSolvQuot G m))).map
          ((H : Subgroup (MaxSolvQuot G m)).subtype)) :
    containsLastDerived (G := G) m H N :=
  (containsLastDerived_iff_lastDerivedSubgroup_le_map_subtype
    (G := G) (m := m) (H := H) (N := N)).2 hN


/--
Trivial closed commutator subgroup makes the natural map to topological abelianization
injective.
-/
theorem injective_topologicalAbelianizationMk_of_topologicalCommutator_eq_bot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hcomm : topologicalCommutator G = ⊥) :
    Function.Injective (TopologicalAbelianization.mk G) := by
  rw [← MonoidHom.ker_eq_bot_iff, TopologicalAbelianization.ker_mk]
  simpa [topologicalCommutator] using hcomm

/--
Trivial first closed derived subgroup makes the natural map to topological abelianization
injective.
-/
theorem injective_topologicalAbelianizationMk_of_topDerivedTop_one_eq_bot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hder : topDerivedTop G 1 = ⊥) :
    Function.Injective (TopologicalAbelianization.mk G) :=
  injective_topologicalAbelianizationMk_of_topologicalCommutator_eq_bot (G := G) <| by
    simpa using hder

/--
If the first closed derived subgroup of a closed subgroup vanishes in the ambient group, then
the subgroup has trivial first closed derived subgroup internally as well.
-/
theorem topDerivedTop_one_eq_bot_of_closedDerivedSeries_eq_bot
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    {K : Subgroup Q} (hKClosed : IsClosed (K : Set Q))
    (hstep : closedDerivedSeries (G := Q) K 1 = ⊥) :
    topDerivedTop K 1 = ⊥ := by
  have hmapTop : (⊤ : Subgroup K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, by simp only [Subgroup.coe_top, Set.mem_univ], rfl⟩
  have hmap :
      (topDerivedTop K 1).map K.subtype = closedDerivedSeries (G := Q) K 1 := by
    calc
      (topDerivedTop K 1).map K.subtype =
          closedDerivedSeries (G := Q) ((⊤ : Subgroup K).map K.subtype) 1 := by
            simpa [topDerivedTop] using
              (topDerived_one_map_subtype_eq_of_isClosed_subgroup
                (G := Q) (H := K) (K := (⊤ : Subgroup K)) hKClosed)
      _ = closedDerivedSeries (G := Q) K 1 := by simp only [hmapTop, closedDerivedSeries_succ,
          closedDerivedSeries_zero]
  have hstep' : closedCommutator K K = ⊥ := by
    simpa [closedDerivedSeries] using hstep
  have hmapbot : (topDerivedTop K 1).map K.subtype = ⊥ := by
    simpa [hstep'] using hmap
  exact
    (Subgroup.map_eq_bot_iff_of_injective
      (H := topDerivedTop K 1)
      (f := K.subtype)
      (by
        intro x y hxy
        exact Subtype.ext hxy)).1 hmapbot

/--
The kernel of the canonical topological abelianization map is the first closed derived subgroup.
-/
theorem topologicalAbelianization_profiniteKernelSubgroup_eq_topDerivedTop_one
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    ProCGroups.ProC.ProfiniteKernelSubgroup
        (TopologicalAbelianization.mkₜ G) =
      topDerivedTop G 1 := by
  ext y
  change TopologicalAbelianization.mk G y = 1 ↔ y ∈ topDerivedTop G 1
  rw [TopologicalAbelianization.mk_eq_one_iff]
  simp only [Subgroup.closedCommutator, topologicalCommutator_eq_closedCommutator_top_top,
    closedCommutator, topDerivedTop, closedDerivedSeries]

/--
Mapping the first closed derived subgroup of the topological abelianization kernel back into the
ambient group gives the second closed derived subgroup.
-/
theorem topologicalAbelianization_kernel_closedDerivedSeries_one_map_subtype_eq_topDerivedTop_two
    (G : Type u) [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    let N : Subgroup G :=
      ProCGroups.ProC.ProfiniteKernelSubgroup (TopologicalAbelianization.mkₜ G)
    (closedDerivedSeries (G := N) (⊤ : Subgroup N) 1).map N.subtype =
      topDerivedTop G 2 := by
  let N : Subgroup G :=
    ProCGroups.ProC.ProfiniteKernelSubgroup (TopologicalAbelianization.mkₜ G)
  have hN_eq : N = topDerivedTop G 1 :=
    topologicalAbelianization_profiniteKernelSubgroup_eq_topDerivedTop_one G
  have hNmap : (⊤ : Subgroup N).map N.subtype = topDerivedTop G 1 := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      change (z : G) ∈ topDerivedTop G 1
      exact hN_eq ▸ z.2
    · intro hy
      refine ⟨⟨y, hN_eq.symm ▸ hy⟩, by simp only [Subgroup.coe_top, Set.mem_univ], rfl⟩
  have hmap :
      (closedDerivedSeries (G := N) (⊤ : Subgroup N) 1).map N.subtype =
        closedDerivedSeries (G := G) ((⊤ : Subgroup N).map N.subtype) 1 := by
    exact
      topDerived_one_map_subtype_eq_of_isClosed_subgroup
        (G := G) (H := N) (K := (⊤ : Subgroup N))
        (by
          simpa [N] using
            ProCGroups.ProC.isClosed_profiniteKernelSubgroup
              (TopologicalAbelianization.mkₜ G))
  calc
    (closedDerivedSeries (G := N) (⊤ : Subgroup N) 1).map N.subtype =
        closedDerivedSeries (G := G) ((⊤ : Subgroup N).map N.subtype) 1 := hmap
    _ = closedDerivedSeries (G := G) (topDerivedTop G 1) 1 := by rw [hNmap]
    _ = topDerivedTop G 2 := by
      change closedDerivedSeries (G := G) (topDerivedTop G 1) 1 = topDerivedTop G (1 + 1)
      exact topDerived_add (G := G) (m := 1) (n := 1)

/--
Membership in the second closed derived subgroup is equivalent to membership in the closed
commutator of the canonical topological abelianization kernel.
-/
theorem mem_topDerivedTop_two_iff_mem_closedCommutator_topologicalAbelianizationKernel
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {a : G}
    (haψ : TopologicalAbelianization.mkₜ G a = 1) :
    a ∈ topDerivedTop G 2 ↔
      (⟨a, haψ⟩ : ProCGroups.ProC.ProfiniteKernelSubgroup
        (TopologicalAbelianization.mkₜ G)) ∈
        Subgroup.closedCommutator
          (ProCGroups.ProC.ProfiniteKernelSubgroup
            (TopologicalAbelianization.mkₜ G)) := by
  let N : Subgroup G :=
    ProCGroups.ProC.ProfiniteKernelSubgroup (TopologicalAbelianization.mkₜ G)
  have hmap :
      (closedDerivedSeries (G := N) (⊤ : Subgroup N) 1).map N.subtype =
        topDerivedTop G 2 :=
    topologicalAbelianization_kernel_closedDerivedSeries_one_map_subtype_eq_topDerivedTop_two G
  have hclosed :
      closedDerivedSeries (G := N) (⊤ : Subgroup N) 1 =
        Subgroup.closedCommutator N :=
    closedDerivedSeries_top_one_eq_closedCommutator N
  constructor
  · intro ha
    have ha_map :
        a ∈ (closedDerivedSeries (G := N) (⊤ : Subgroup N) 1).map N.subtype := by
      rwa [hmap]
    rcases ha_map with ⟨z, hz, hza⟩
    have hz_eq : z = (⟨a, haψ⟩ : N) := by
      apply Subtype.ext
      simpa using hza
    rw [hclosed] at hz
    change (⟨a, haψ⟩ : N) ∈ Subgroup.closedCommutator N
    rw [← hz_eq]
    exact hz
  · intro ha
    have ha_map :
        a ∈ (closedDerivedSeries (G := N) (⊤ : Subgroup N) 1).map N.subtype := by
      refine ⟨(⟨a, haψ⟩ : N), ?_, rfl⟩
      rw [hclosed]
      change (⟨a, haψ⟩ : N) ∈ Subgroup.closedCommutator N at ha
      exact ha
    rwa [hmap] at ha_map

end ProCGroups.FiniteStepSolvableQuotients
