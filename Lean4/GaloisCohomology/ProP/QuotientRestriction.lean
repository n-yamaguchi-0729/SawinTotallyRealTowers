import GaloisCohomology.ProP.TrivialZModP
import Mathlib.Topology.Algebra.Group.Quotient

set_option autoImplicit false
open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The continuous quotient projection, without any openness assumption on the normal subgroup. -/
def quotientProjection (N : Subgroup G) [N.Normal] : G →ₜ* G ⧸ N where
  toMonoidHom := QuotientGroup.mk' N
  continuous_toFun := QuotientGroup.continuous_mk

/-- The continuous inclusion of a subgroup. -/
def subgroupInclusion (N : Subgroup G) : N →ₜ* G where
  toMonoidHom := N.subtype
  continuous_toFun := continuous_subtype_val

/-- The constant-one continuous homomorphism. -/
def trivialContinuousHom
    (H : Type v) (K : Type w) [Group H] [TopologicalSpace H]
    [Group K] [TopologicalSpace K] : H →ₜ* K where
  toMonoidHom := 1
  continuous_toFun := continuous_const

@[simp]
theorem quotientProjection_comp_subgroupInclusion (N : Subgroup G) [N.Normal] :
    (quotientProjection N).comp (subgroupInclusion N) =
      trivialContinuousHom N (G ⧸ N) := by
  ext x
  exact (QuotientGroup.eq_one_iff (N := N) (x : G)).2 x.2

section Small

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (p : ℕ)

/-- At the maintained cohomology API level, inflation followed by restriction is the map induced
by the constant-one group homomorphism.  Proving that this map is zero in positive degree is the
first missing source lemma needed even before constructing transgression. -/
theorem inflation_comp_restriction_eq_trivialMap
    (N : Subgroup G) [N.Normal] (n : ℕ) :
    continuousCohomologyZModPMap p (quotientProjection N) n ≫
        continuousCohomologyZModPMap p (subgroupInclusion N) n =
      continuousCohomologyZModPMap p (trivialContinuousHom N (G ⧸ N)) n := by
  have h := continuousCohomologyZModPMap_comp p
    (quotientProjection N) (subgroupInclusion N) n
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

/-- The corresponding source-level factorization on homogeneous cochains. -/
theorem cochains_inflation_comp_restriction_eq_trivialMap
    (N : Subgroup G) [N.Normal] :
    trivialZModPCochainsMap p (quotientProjection N) ≫
        trivialZModPCochainsMap p (subgroupInclusion N) =
      trivialZModPCochainsMap p (trivialContinuousHom N (G ⧸ N)) := by
  have h := trivialZModPCochainsMap_comp p
    (quotientProjection N) (subgroupInclusion N)
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
    continuousCohomologyZModPMapLifted p (quotientProjection N) n ≫
        continuousCohomologyZModPMapLifted p (subgroupInclusion N) n =
      continuousCohomologyZModPMapLifted p (trivialContinuousHom N (G ⧸ N)) n := by
  have h := continuousCohomologyZModPMapLifted_comp p
    (quotientProjection N) (subgroupInclusion N) n
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

/-- The lifted source-level factorization on homogeneous cochains. -/
theorem cochains_inflation_comp_restriction_eq_trivialMap_lifted
    (N : Subgroup G) [N.Normal] :
    trivialZModPCochainsMapLifted p (quotientProjection N) ≫
        trivialZModPCochainsMapLifted p (subgroupInclusion N) =
      trivialZModPCochainsMapLifted p (trivialContinuousHom N (G ⧸ N)) := by
  have h := trivialZModPCochainsMapLifted_comp p
    (quotientProjection N) (subgroupInclusion N)
  rw [quotientProjection_comp_subgroupInclusion] at h
  exact h.symm

end Lifted

end

end ClassFieldTower.Cohomology
