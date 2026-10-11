/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.InverseLimits.Predicates

/-!
# Abelian open-normal quotient bases

This file proves that a profinite group with an abelian open-normal quotient basis is itself
abelian. The proof tests commutators in all open normal quotients and then uses profinite
separation.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

section

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

namespace HasAbelianOpenNormalBasis

omit [T2Space G] in
/-- A profinite group with an abelian open-normal quotient basis is abelian. -/
theorem isAbelian (hG : HasAbelianOpenNormalBasis G) : ∀ a b : G, a * b = b * a := by
  intro a b
  have hcomm_mem : ∀ U : OpenNormalSubgroup G, a * b * a⁻¹ * b⁻¹ ∈ (U : Subgroup G) := by
    intro U
    have hab :
        QuotientGroup.mk' (U : Subgroup G) a * QuotientGroup.mk' (U : Subgroup G) b =
          QuotientGroup.mk' (U : Subgroup G) b * QuotientGroup.mk' (U : Subgroup G) a :=
      (hG.quotient_mem FiniteGroupClass.abelian_formation U).2 _ _
    refine (QuotientGroup.eq_one_iff (N := (U : Subgroup G)) _).1 ?_
    have h :=
      congrArg (fun z : G ⧸ (U : Subgroup G) =>
        z * ((QuotientGroup.mk' (U : Subgroup G) a)⁻¹ *
          (QuotientGroup.mk' (U : Subgroup G) b)⁻¹)) hab
    simpa [map_mul, mul_assoc] using h
  have hcomm_one : a * b * a⁻¹ * b⁻¹ = 1 := by
    apply ProfiniteGrp.eq_one_of_mem_all_openNormalSubgroups (G := G)
    intro U
    exact hcomm_mem U
  have h1 : a * b * a⁻¹ = b := by
    have h := congrArg (fun x : G => x * b) hcomm_one
    simpa [mul_assoc] using h
  have h2 : a * b = b * a := by
    have h := congrArg (fun x : G => x * a) h1
    simpa [mul_assoc] using h
  exact h2

end HasAbelianOpenNormalBasis
end

end ProCGroups.ProC
