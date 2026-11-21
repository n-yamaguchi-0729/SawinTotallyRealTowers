/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.Topologies.ContinuousMonoidHom
public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Quotient inflation followed by subgroup restriction

The composite of the continuous quotient projection and subgroup inclusion
induces the constant-one map on cochains and cohomology.
-/

@[expose] public section

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The quotient projection sends every element of its defining subgroup to one. -/
@[simp]
theorem quotientProjection_comp_subgroupInclusion (N : Subgroup G) [N.Normal] :
    (ProCGroups.ContinuousMonoidHom.quotientMk N).comp (ProCGroups.ContinuousMonoidHom.subtype N) =
      1 := by
  ext x
  exact (QuotientGroup.eq_one_iff (N := N) (x : G)).2 x.2

section Small

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (p : ℕ)

/-- Inflation followed by restriction is induced by the constant-one group homomorphism. -/
theorem inflation_comp_restriction_eq_trivialMap
    (N : Subgroup G) [N.Normal] (n : ℕ) :
    continuousCohomologyZModPMap p (ProCGroups.ContinuousMonoidHom.quotientMk N) n ≫
        continuousCohomologyZModPMap p (ProCGroups.ContinuousMonoidHom.subtype N) n =
      continuousCohomologyZModPMap p (1 : N →ₜ* G ⧸ N) n := by
  have h := continuousCohomologyZModPMap_comp p
    (ProCGroups.ContinuousMonoidHom.quotientMk N) (ProCGroups.ContinuousMonoidHom.subtype N) n
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

/-- The corresponding source-level factorization on homogeneous cochains. -/
theorem cochains_inflation_comp_restriction_eq_trivialMap
    (N : Subgroup G) [N.Normal] :
    trivialZModPCochainsMap p (ProCGroups.ContinuousMonoidHom.quotientMk N) ≫
        trivialZModPCochainsMap p (ProCGroups.ContinuousMonoidHom.subtype N) =
      trivialZModPCochainsMap p (1 : N →ₜ* G ⧸ N) := by
  have h := trivialZModPCochainsMap_comp p
    (ProCGroups.ContinuousMonoidHom.quotientMk N) (ProCGroups.ContinuousMonoidHom.subtype N)
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

end Small

section Lifted

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (p : ℕ)

/-- Inflation followed by restriction for universe-lifted trivial coefficients is induced by the
constant-one group homomorphism. -/
theorem inflation_comp_restriction_eq_trivialMap_lifted
    (N : Subgroup G) [N.Normal] (n : ℕ) :
    continuousCohomologyZModPMapLifted p (ProCGroups.ContinuousMonoidHom.quotientMk N) n ≫
        continuousCohomologyZModPMapLifted p (ProCGroups.ContinuousMonoidHom.subtype N) n =
      continuousCohomologyZModPMapLifted p (1 : N →ₜ* G ⧸ N) n := by
  have h := continuousCohomologyZModPMapLifted_comp p
    (ProCGroups.ContinuousMonoidHom.quotientMk N) (ProCGroups.ContinuousMonoidHom.subtype N) n
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

/-- The lifted source-level factorization on homogeneous cochains. -/
theorem cochains_inflation_comp_restriction_eq_trivialMap_lifted
    (N : Subgroup G) [N.Normal] :
    trivialZModPCochainsMapLifted p (ProCGroups.ContinuousMonoidHom.quotientMk N) ≫
        trivialZModPCochainsMapLifted p (ProCGroups.ContinuousMonoidHom.subtype N) =
      trivialZModPCochainsMapLifted p (1 : N →ₜ* G ⧸ N) := by
  have h := trivialZModPCochainsMapLifted_comp p
    (ProCGroups.ContinuousMonoidHom.quotientMk N) (ProCGroups.ContinuousMonoidHom.subtype N)
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

end Lifted

end

end ClassFieldTower.Cohomology
